"""Lean import minimiser: one entry point for every stage. See README.md.

Every stage is run the same way: `run STAGE` decides the new import lists by compiling
and writes them to work/STAGE/result.json without touching the sources; `apply STAGE`
writes them into the sources.

Stages:
  implied   1a  drop imports implied by another import of the same file (graph only)
  remove    1b  drop every import that the file and all its dependents compile without
  direct    2   every import must itself provide something the file uses
  private   3   every import gets the weakest modifier that compiles

Usage:
  impmin.py run STAGE [--limit N] [--fresh] [--no-guess]
  impmin.py apply STAGE [--apply [--build]]  dry run without --apply; --build: lake build
  impmin.py format [--apply]               Mathlib-style import blocks, same imports
  impmin.py verify-diff [--table]          working tree == HEAD minus import lines?
  impmin.py baseline                       compile every file once (timeouts)
  impmin.py shadow                         recreate the shadow olean tree
  impmin.py selftest                       check that the shadow tree works
"""
import argparse
import concurrent.futures as cf
import fcntl
import hashlib
import itertools
import json
import os
import re
import shutil
import signal
import subprocess
import sys
import threading
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from impgraph import (OPTS, LEAN, ROOT, ROOT_MODULE, Graph, HeaderError,  # noqa: E402
                      body_sha, mod_path, new_source, parse_line, project_header,
                      project_modules, rewrite, scan_header, short, work_modules,
                      write_atomic)

STAGES = ("implied", "remove", "direct", "private")
WORKERS = int(os.environ.get("IMPMIN_WORKERS", "4"))  # lean processes at once, globally
# Stage 1b: after the removals of a file are decided, also compile every dependent whose
# visible modules did not change (its olean inputs did). Costs one batch per file. The
# root file is compiled at that point either way.
FULL_DEPENDENT_CHECK = True
WORK = HERE + "/work"
TIMES = WORK + "/base_times.json"
BUILD_LIB = ROOT + "/.lake/build/lib/lean"
IMPMIN = ROOT + "/.lake/import-min"
SHADOW = IMPMIN + "/lean"
SHADOW_OWNER = IMPMIN + "/owner"
LOCK = IMPMIN + "/lock"
TMP = IMPMIN + "/tmp"  # trial sources, outputs, backups; same filesystem as the shadow
ART_EXTS = (".olean", ".olean.server", ".olean.private", ".ir", ".ir.sig", ".ilean")

_print_lock = threading.Lock()
_progress = [None]  # file that `say` copies its lines to


def say(*a):
    line = " ".join([time.strftime("%H:%M:%S")] + [str(x) for x in a])
    with _print_lock:
        print(line, flush=True)
        if _progress[0]:
            with open(_progress[0], "a") as f:
                f.write(line + "\n")


def dump(obj, path):
    tmp = path + ".tmp"
    with open(tmp, "w") as f:
        json.dump(obj, f, indent=1)
        f.flush()
        os.fsync(f.fileno())
    os.replace(tmp, path)


def load_json(path, default=None):
    if not os.path.exists(path):
        return default
    with open(path) as f:
        return json.load(f)


def stage_dir(stage):
    return f"{WORK}/{stage}"


def rel(mod):
    return mod.replace(".", "/")


def texts_of(imps):
    return [e["text"] for e in imps]


# ------------------------------------------------------- locking and shadow guards
_lock_fd = [None]


def take_lock(what):
    """One impmin process per target at a time (held until the process exits)."""
    if _lock_fd[0] is not None:
        return
    os.makedirs(IMPMIN, exist_ok=True)
    fd = os.open(LOCK, os.O_RDWR | os.O_CREAT, 0o644)
    try:
        fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError:
        os.close(fd)
        sys.exit(f"another impmin process is working on {ROOT}; not running {what}")
    _lock_fd[0] = fd


def shadow_owner():
    if not os.path.isdir(SHADOW) or not os.path.exists(SHADOW_OWNER):
        return None
    with open(SHADOW_OWNER) as f:
        return f.read().strip()


def unfinished_run():
    """The stage whose unfinished run owns the shadow tree, if any."""
    owner = shadow_owner()
    if owner not in STAGES:
        return None
    res = load_json(stage_dir(owner) + "/result.json")
    if res is not None and len(res) < len(work_modules()):
        return owner
    return None


def refuse_if_unfinished(what, allow=None):
    busy = unfinished_run()
    if busy and busy != allow:
        sys.exit(f"not running {what}: the unfinished `{busy}` run uses the shadow tree. "
                 f"Finish it (`impmin.py run {busy}`) or discard it (`rm -rf {IMPMIN}`).")


# ----------------------------------------------------------------- environment
_env_cache = {}
_env_lock = threading.Lock()


def lake_env(shadow):
    with _env_lock:
        if "base" not in _env_cache:
            out = subprocess.run(["lake", "env", "env", "-0"], cwd=ROOT, capture_output=True,
                                 check=True).stdout.decode("utf-8", "replace")
            _env_cache["base"] = dict(kv.split("=", 1) for kv in out.split("\0") if "=" in kv)
    env = dict(_env_cache["base"])
    if shadow:
        parts = env["LEAN_PATH"].split(":")
        assert BUILD_LIB in parts, parts
        env["LEAN_PATH"] = ":".join(SHADOW if p == BUILD_LIB else p for p in parts)
    return env


def build_is_current():
    return subprocess.run(["lake", "build", "--no-build"], cwd=ROOT, capture_output=True
                          ).returncode == 0


def check_opts(work):
    """OPTS must be the options Lake compiles with (recorded in its .setup.json files)."""
    for m in work:
        p = f"{ROOT}/.lake/build/ir/{rel(m)}.setup.json"
        if os.path.exists(p):
            break
    else:
        say("note: no Lake .setup.json found; cannot check OPTS against the lakefile")
        return
    fmt = lambda v: ("true" if v else "false") if isinstance(v, bool) else str(v)  # noqa
    want = sorted(f"-D{k}={fmt(v)}" for k, v in load_json(p).get("options", {}).items())
    if want != sorted(OPTS):
        sys.exit(f"OPTS in impgraph.py do not match the options Lake uses ({p}):\n"
                 f"  OPTS: {sorted(OPTS)}\n  Lake: {want}")


# --------------------------------------------------------------------- running
_slots = threading.BoundedSemaphore(WORKERS)  # lean processes at once, over all threads
# On a pipe, lean's stdout is block-buffered: the first error would only arrive at exit,
# and "kill at the first error" would save nothing. stdbuf execs lean (same pid) with
# line-buffered stdout.
LINEBUF = ["stdbuf", "-oL"] if shutil.which("stdbuf") else []
_shutdown = threading.Event()  # set on Ctrl-C: no compile result may be used any more
_live = set()
_live_lock = threading.Lock()


def kill(p):
    """SIGKILL the lean process `p` unless run_lean has reaped it already. (Popen.kill
    is not used: it polls first and can reap the child behind run_lean's wait4.)"""
    with p.impmin_lock:
        if p.impmin_alive:
            try:
                os.kill(p.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass


def interrupt_all():
    _shutdown.set()
    with _live_lock:
        procs = list(_live)
    for p in procs:
        kill(p)


class Interrupted(Exception):
    pass


class CompileCrash(RuntimeError):
    """A compile ended without a Lean error (timeout, signal, crash) even when retried."""


class Batch:
    """Run compile jobs on a small pool, optionally stopping at the first failure."""

    def __init__(self, failfast=False):
        self.failfast = failfast
        self.cancel = threading.Event()
        self.procs = set()
        self.lock = threading.Lock()

    def register(self, p):
        with self.lock:
            self.procs.add(p)
        if self.cancel.is_set():
            kill(p)

    def unregister(self, p):
        with self.lock:
            self.procs.discard(p)

    def abort(self):
        self.cancel.set()
        with self.lock:
            procs = list(self.procs)
        for p in procs:
            kill(p)

    def run(self, jobs):
        """jobs: list of (key, callable(batch) -> result dict). Returns {key: result};
        jobs cancelled by a failfast abort are left out."""
        results = {}

        def wrap(kf):
            key, fn = kf
            if self.cancel.is_set() or _shutdown.is_set():
                return key, None
            r = fn(self)
            if self.failfast and r is not None and not r["ok"] and not r.get("cancelled"):
                self.abort()
            return key, r

        with cf.ThreadPoolExecutor(max_workers=WORKERS) as ex:
            try:
                for key, r in ex.map(wrap, jobs):
                    if r is not None and not r.get("cancelled"):
                        results[key] = r
            except BaseException as e:
                if isinstance(e, KeyboardInterrupt):
                    interrupt_all()
                self.abort()
                raise
        return results


def run_lean(args, env, timeout, batch=None):
    """Run `lean`, killing it at the first error message.

    status: "ok"; "error" (Lean reported an error: the only real "does not compile");
    "timeout" / "crash" (no Lean error: killed by a signal, non-zero exit, raw output);
    "cancelled" (killed by us: failfast abort or Ctrl-C)."""
    with _slots:
        if _shutdown.is_set() or (batch and batch.cancel.is_set()):
            return dict(ok=False, status="cancelled", cancelled=True, secs=0, rss_mb=0,
                        err=None, warnings=0)
        t0 = time.time()
        p = subprocess.Popen(LINEBUF + [LEAN] + args, cwd=ROOT, env=env,
                             stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                             encoding="utf-8", errors="replace")
        p.impmin_lock = threading.Lock()
        p.impmin_alive = True
        with _live_lock:
            _live.add(p)
        if batch:
            batch.register(p)
        timed_out = []

        def on_timeout():
            timed_out.append(1)
            kill(p)

        timer = threading.Timer(timeout, on_timeout)
        timer.daemon = True
        timer.start()
        err = raw = None
        nwarn = 0
        try:
            for line in p.stdout:
                if line.startswith("{"):
                    try:
                        msg = json.loads(line)
                    except ValueError:
                        raw = raw or line.strip()[:500]
                        continue
                    sev = msg.get("severity")
                    if sev == "error":
                        pos = msg.get("pos") or {}
                        err = f'{pos.get("line")}:{pos.get("column")}: ' + \
                            " ".join(str(msg.get("data", "")).split())[:1000]
                        kill(p)
                        break
                    if sev == "warning":
                        nwarn += 1
                elif line.strip():
                    raw = raw or line.strip()[:500]
        except BaseException:
            kill(p)
            raise
        finally:
            timer.cancel()
            with _live_lock:
                _live.discard(p)
            if batch:
                batch.unregister(p)
            p.stdout.close()
            # Only reached once the process is exiting (stdout closed) or killed, so
            # holding the lock while waiting is safe; after this nobody may signal the pid.
            with p.impmin_lock:
                try:
                    _, status, ru = os.wait4(p.pid, 0)
                    p.returncode, rss = os.waitstatus_to_exitcode(status), ru.ru_maxrss // 1024
                except ChildProcessError:  # reaped elsewhere; should not happen
                    p.returncode, rss = (p.returncode if p.returncode is not None else -1), 0
                p.impmin_alive = False
    rc = p.returncode
    killed_by_us = _shutdown.is_set() or bool(batch and batch.cancel.is_set())
    if err is not None:
        st = "error"
    elif timed_out:
        st, err = "timeout", f"timeout after {timeout:.0f}s"
    elif rc != 0 and killed_by_us:
        st = "cancelled"
    elif rc != 0 or raw:
        st, err = "crash", f"exit code {rc}" + (f"; output: {raw}" if raw else "")
    else:
        st = "ok"
    return dict(ok=st == "ok", status=st, cancelled=st == "cancelled",
                secs=round(time.time() - t0, 1), rss_mb=rss, err=err,
                warnings=nwarn)


_tags = itertools.count(1)


def new_tag():
    return f"{os.getpid()}_{next(_tags)}"


def compile_mod(mod, imports=None, out=False, shadow=True, timeout=1800, batch=None,
                extra="", reformat=False):
    """Compile `mod`.

    imports:  if given, a temporary copy of the source with these import lines is
              compiled, the block rewritten exactly as `apply` would (`reformat`).
    out:      if True, write the olean family into a fresh directory, returned as "outdir".
    extra:    text appended to the source (used only by the self-test).
    """
    tag = new_tag()
    srcroot = outdir = r = None
    try:
        if imports is not None or extra:
            if imports is None:
                with open(mod_path(mod), encoding="utf-8") as f:
                    text = f.read()
            else:
                text = new_source(mod, imports, reformat)
            srcroot = f"{TMP}/src/{tag}"
            path = f"{srcroot}/{rel(mod)}.lean"
            os.makedirs(os.path.dirname(path), exist_ok=True)
            with open(path, "w", encoding="utf-8") as f:
                f.write(text + extra)
            args = ["-R", srcroot, path]
        else:
            args = ["-R", ROOT, mod_path(mod)]
        if out:
            outdir = f"{TMP}/out/{tag}"
            base = f"{outdir}/{rel(mod)}"
            os.makedirs(os.path.dirname(base), exist_ok=True)
            args += ["-o", base + ".olean", "-i", base + ".ilean"]
        args += ["--json"] + OPTS
        r = run_lean(args, lake_env(shadow), timeout, batch)
    finally:
        if srcroot:
            shutil.rmtree(srcroot, ignore_errors=True)
        if outdir and not (r and r["ok"]):
            shutil.rmtree(outdir, ignore_errors=True)
            outdir = None
    r["outdir"] = outdir
    return r


# ---------------------------------------------------------------------- shadow
def make_shadow(owner):
    """Hardlink copy of the real build that recompiled oleans are installed into.
    The owner file is removed first and written last, so a failed copy owns nothing."""
    if os.path.exists(SHADOW_OWNER):
        os.remove(SHADOW_OWNER)
    if os.path.isdir(SHADOW):
        shutil.rmtree(SHADOW)
    os.makedirs(IMPMIN, exist_ok=True)
    subprocess.run(["cp", "-al", BUILD_LIB, SHADOW], check=True)
    with open(SHADOW_OWNER + ".tmp", "w") as f:
        f.write(owner)
    os.replace(SHADOW_OWNER + ".tmp", SHADOW_OWNER)


def art_files(base):
    return [base + e for e in ART_EXTS if os.path.exists(base + e)]


def install(mod, outdir):
    """Move freshly compiled artifacts of `mod` into the shadow; return backup dir."""
    bdir = f"{TMP}/backup/{new_tag()}"
    src_base = f"{outdir}/{rel(mod)}"
    dst_base = f"{SHADOW}/{rel(mod)}"
    os.makedirs(os.path.dirname(f"{bdir}/{rel(mod)}"), exist_ok=True)
    produced = art_files(src_base)
    assert src_base + ".olean" in produced, produced
    for f in produced:
        ext = f[len(src_base):]
        if os.path.exists(dst_base + ext):
            os.replace(dst_base + ext, f"{bdir}/{rel(mod)}{ext}")
        os.replace(f, dst_base + ext)  # rename: never writes through the hardlink
    shutil.rmtree(outdir, ignore_errors=True)
    return bdir


def restore(mod, bdir):
    src_base = f"{bdir}/{rel(mod)}"
    dst_base = f"{SHADOW}/{rel(mod)}"
    for f in art_files(src_base):
        os.replace(f, dst_base + f[len(src_base):])
    shutil.rmtree(bdir, ignore_errors=True)


def reset_shadow_module(mod):
    """Point the shadow's artifacts of `mod` back at the real build."""
    if not os.path.exists(f"{BUILD_LIB}/{rel(mod)}.olean"):
        raise RuntimeError(f"{mod} has no olean in {BUILD_LIB} (was the build cleaned?)")
    for ext in ART_EXTS:
        s, d = f"{BUILD_LIB}/{rel(mod)}{ext}", f"{SHADOW}/{rel(mod)}{ext}"
        if os.path.exists(s):
            tmp = d + ".tmp"
            if os.path.exists(tmp):
                os.remove(tmp)
            os.link(s, tmp)
            os.replace(tmp, d)
        elif os.path.exists(d):
            os.remove(d)


def sha(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


# -------------------------------------------------------------------- baseline
def cmd_baseline():
    work = work_modules()
    os.makedirs(WORK, exist_ok=True)
    jobs = [(m, lambda b, m=m: compile_mod(m, shadow=False, batch=b)) for m in work]
    t0 = time.time()
    res = Batch().run(jobs)
    wall = time.time() - t0
    bad = {m: r["err"] for m, r in res.items() if not r["ok"]}
    dump(dict(root=ROOT, files={m: dict(secs=r["secs"], rss_mb=r["rss_mb"],
                                        warnings=r["warnings"], ok=r["ok"])
                                for m, r in res.items()}), TIMES)
    cpu = sum(r["secs"] for r in res.values())
    say(f"baseline: {len(res)} files, wall {wall:.0f}s with {WORKERS} workers, "
        f"sum of per-file times {cpu:.0f}s, max RSS {max(r['rss_mb'] for r in res.values())} MB")
    for m, r in sorted(res.items(), key=lambda kv: -kv[1]["secs"])[:10]:
        say(f"   {r['secs']:7.1f}s {r['rss_mb']:5d}MB  {m}")
    if bad:
        say("FAILED:", json.dumps(bad, indent=1))
        sys.exit(1)


def load_times():
    """Per-file baseline times; (re)runs `baseline` if any file is missing or failed."""
    t = load_json(TIMES) or {}
    files = t.get("files", {}) if t.get("root") == ROOT else {}
    if any(m not in files or not files[m]["ok"] for m in work_modules()):
        say("no successful baseline for every file yet: running `baseline`")
        cmd_baseline()
        files = load_json(TIMES)["files"]
    return files


def cmd_selftest():
    """Is an olean installed in the shadow really the one dependents load?"""
    take_lock("selftest")
    refuse_if_unfinished("selftest")
    g = Graph()
    times = load_times()
    work = set(g.work)
    pairs = [(e["mod"], C) for C in g.work for e in g.imports(C)
             if e["mod"] in work and not e["meta"]]
    B, C = min(pairs, key=lambda bc: times[bc[0]]["secs"] + times[bc[1]]["secs"])
    say(f"probe: B = {B}, C = {C} (C imports B)")
    make_shadow("selftest")
    real = f"{BUILD_LIB}/{rel(B)}.olean"
    before = sha(real)
    probe = "\n\npublic theorem impminProbeXyz : True := trivial\n"
    use = "\n\nexample : True := impminProbeXyz\n"
    r = compile_mod(B, out=True, extra=probe)
    say("compile B with probe:", r["ok"], r["secs"], "s", r["err"])
    if not r["ok"]:
        sys.exit(1)
    r0 = compile_mod(C, extra=use)
    say("C using probe BEFORE install (must fail):", r0["ok"], r0["err"])
    bdir = install(B, r["outdir"])
    r1 = compile_mod(C, extra=use)
    say("C using probe AFTER install (must pass):", r1["ok"], r1["secs"], "s", r1["err"])
    restore(B, bdir)
    r2 = compile_mod(C, extra=use)
    say("C using probe AFTER restore (must fail):", r2["ok"], r2["err"])
    same_inode = os.stat(real).st_ino == os.stat(f"{SHADOW}/{rel(B)}.olean").st_ino
    say("real build olean untouched:", sha(real) == before,
        "| shadow is hardlink of real again:", same_inode)
    ok = r0["status"] == "error" and r1["ok"] and r2["status"] == "error" and \
        sha(real) == before and same_inode
    say("SELFTEST", "PASSED" if ok else "FAILED")
    sys.exit(0 if ok else 1)


# ---------------------------------------------------------------- stage driver
class Stage:
    """Common driver: files in topological order, one result entry per file, resumable.

    The sources are never edited during a run. After a file is done, its new imports
    are recorded in the graph and (stages that compile) its new olean is in the shadow,
    so later files are processed against the new state.

    work/STAGE/run.json, written at a fresh start, records the original import lines and
    a hash of the rest of every file. Resuming and `apply` check the sources against it,
    and the graph is always rebuilt from the original lines, so a resumed run (also after
    a partial `apply`) decides exactly as an uninterrupted one."""

    name = None
    compiles = True  # False: graph only (no shadow, no build check)
    reformat = False  # trials and `apply` rewrite the whole block (else: delete lines)

    def __init__(self, opts):
        self.opts = opts
        self.dir = stage_dir(self.name)
        self.result_path = self.dir + "/result.json"
        self.run_path = self.dir + "/run.json"
        self.log_path = self.dir + "/log.jsonl"
        take_lock(f"run {self.name}")
        self.base = self.prepare()
        _progress[0] = self.dir + "/progress.out"
        self.meta = load_json(self.run_path)
        self.result = load_json(self.result_path, {})
        self.g = g = Graph()
        for m in g.work:  # the original state, whatever has been applied since
            if sorted(texts_of(g.imports(m))) != sorted(self.meta["orig"][m]):
                g.set_imports(m, [parse_line(t) for t in self.meta["orig"][m]])
        self.orig = {m: project_header(m)[1] for m in g.work}  # current lines (with numbers)
        self.order = g.topo_order()
        self.ncomp = 0
        self.csecs = 0.0
        self.stats = {}  # file -> [compiles, compile seconds]
        self._lock = threading.Lock()
        if self.compiles:
            self.verify_sources()

    # -- set-up ------------------------------------------------------------------
    def prepare(self):
        """Fresh start or resume; see README "Running it". Returns the baseline times."""
        resume = self.compiles and os.path.exists(self.result_path) and \
            os.path.exists(self.run_path) and not self.opts.fresh
        if resume:
            if shadow_owner() != self.name:
                sys.exit(f"cannot resume: the shadow tree is not the one of the interrupted "
                         f"`{self.name}` run (owner: {shadow_owner()}). Start over with --fresh.")
            if load_json(self.run_path).get("root") != ROOT:
                sys.exit(f"cannot resume: {self.dir} belongs to another project")
            print(f"resuming the `{self.name}` run in {self.dir}", flush=True)
        else:
            if self.compiles:
                refuse_if_unfinished(f"a fresh `{self.name}` run", allow=self.name)
                if not build_is_current():
                    sys.exit("`lake build --no-build` fails: run `lake build` first")
            meta = self.snapshot()
            if os.path.isdir(self.dir):
                shutil.rmtree(self.dir)
            os.makedirs(self.dir)
            if self.compiles:
                check_opts(work_modules())
                load_times()
                self.fresh_start()
                make_shadow(self.name)
            dump(meta, self.run_path)
            if self.compiles:
                dump({}, self.result_path)  # the run exists (and is unfinished) from now on
        if self.compiles:
            shutil.rmtree(TMP, ignore_errors=True)
            return load_times()
        return {}

    def snapshot(self):
        """run.json contents: original import lines and body hashes of every file."""
        orig, body, bad = {}, {}, []
        for m in work_modules():
            try:
                lines, imps = project_header(m)
                if self.reformat:
                    rewrite(lines, imps, texts_of(imps), True)  # can `apply` rewrite it?
            except HeaderError as ex:
                bad.append(str(ex))
                continue
            orig[m] = texts_of(imps)
            body[m] = body_sha(lines, imps)
        if bad:
            sys.exit("unsupported import blocks (fix these by hand first):\n  " +
                     "\n  ".join(bad))
        head = subprocess.run(["git", "rev-parse", "HEAD"], cwd=ROOT, capture_output=True,
                              text=True).stdout.strip()
        return dict(root=ROOT, head=head, orig=orig, body=body)

    def verify_sources(self):
        """The sources must still be the ones the run started from (finished files may
        already have their new imports applied)."""
        bad = []
        for m in self.g.work:
            try:
                lines, imps = project_header(m)
            except (HeaderError, OSError) as ex:
                bad.append(str(ex))
                continue
            if body_sha(lines, imps) != self.meta["body"].get(m):
                bad.append(f"{m}: non-import lines changed")
            cur = sorted(texts_of(imps))
            ok = [sorted(self.meta["orig"][m])]
            if m in self.result:
                ok.append(sorted(self.result[m]["new"]))
            if cur not in ok:
                bad.append(f"{m}: import lines changed")
        if bad:
            sys.exit("the sources changed since the run started; restore them or start over "
                     "with --fresh:\n  " + "\n  ".join(bad))

    def fresh_start(self):
        pass

    # -- helpers -----------------------------------------------------------------
    def log(self, **kw):
        kw["t"] = time.time()
        with self._lock:
            with open(self.log_path, "a") as f:
                f.write(json.dumps(kw) + "\n")

    def timeout(self, mod):
        # the root file has no baseline entry; it only loads oleans
        secs = self.base[mod]["secs"] if mod in self.base else \
            max(v["secs"] for v in self.base.values())
        return 3 * secs + 90

    def compile(self, mod, imports=None, out=False, batch=None, owner=None):
        """compile_mod with this stage's settings. A compile that ends without a Lean
        error (timeout, crash, signal) is retried once with twice the time; if that
        fails too, the run stops instead of treating it as "does not compile"."""
        timeout = self.timeout(mod)
        for attempt in (1, 2):
            r = compile_mod(mod, imports, out=out, timeout=timeout, batch=batch,
                            reformat=self.reformat)
            if r["status"] in ("ok", "error", "cancelled"):
                break
            self.log(ev="crash", mod=mod, attempt=attempt, err=r["err"], secs=r["secs"],
                     rss_mb=r["rss_mb"])
            if attempt == 1:
                say(f"    {short(mod)}: {r['err']} (no Lean error); retrying")
                timeout *= 2
        else:
            raise CompileCrash(f"{mod}: compile ended twice without a Lean error: {r['err']}")
        if _shutdown.is_set():
            raise Interrupted()
        if not r["cancelled"]:
            with self._lock:
                self.ncomp += 1
                self.csecs += r["secs"]
                s = self.stats.setdefault(owner or mod, [0, 0.0])
                s[0] += 1
                s[1] += r["secs"]
        return r

    # -- main loop ---------------------------------------------------------------
    def run(self):
        for D in self.order:  # replay finished files so the graph and the shadow agree
            if D in self.result:
                self.g.set_imports(D, [parse_line(t) for t in self.result[D]["new"]])
        todo = [D for D in self.order if D not in self.result]
        if self.opts.limit is not None:
            todo = todo[:self.opts.limit]
        self.t0 = time.time()
        self.run_files(todo)
        done = [D for D in self.order if D in self.result]
        old = sum(len(self.result[D]["old"]) for D in done)
        new = sum(len(self.result[D]["new"]) for D in done)
        finished = len(done) == len(self.order)
        ok = not finished or not self.compiles or self.final_check()
        say(f"{self.name}: {len(done)}/{len(self.order)} files done; import lines of these "
            f"{old} -> {new}; this session {self.ncomp} compiles, {self.csecs:.0f}s compile "
            f"time, {time.time() - self.t0:.0f}s wall")
        if not ok:
            sys.exit(f"final check failed: {ROOT_MODULE} does not compile against the new "
                     f"state (see {self.dir}/final.json); `apply` refuses this result")
        if finished:
            say(f"next: `impmin.py apply {self.name}` (dry run), then with --apply --build")

    def final_check(self):
        """Compile the root file against the final shadow. It is the only module that loads
        every file at once, so it catches clashes between files that no file sees on its
        own (e.g. two auto-named instances that now get the same name). Recorded in
        final.json; `apply` refuses a result whose check failed."""
        path = self.dir + "/final.json"
        if (load_json(path) or {}).get("ok"):
            return True
        say(f"final check: compiling {ROOT_MODULE} against the final state of every file")
        r = self.compile(ROOT_MODULE)
        dump(dict(ok=r["ok"], err=r["err"], secs=r["secs"]), path)
        say(f"final check: {'passed' if r['ok'] else 'FAILED: ' + str(r['err'])}")
        return r["ok"]

    def run_files(self, todo):
        """Process `todo` one file after the other."""
        for D in todo:
            self.verify_sources()
            self.finish(D, self.process_counted(D))

    def process_counted(self, D):
        w0 = time.time()
        st = self.process(D)
        with self._lock:
            n, secs = self.stats.pop(D, [0, 0.0])
        st.update(old=self.meta["orig"][D], compiles=n, compile_secs=round(secs, 1),
                  wall=round(time.time() - w0, 1))
        return st

    def finish(self, D, st):
        self.g.set_imports(D, [parse_line(t) for t in st["new"]])
        self.result[D] = st
        dump(self.result, self.result_path)
        say(f"[{len(self.result)}/{len(self.order)}] {short(D)}: {len(st['old'])} -> "
            f"{len(st['new'])} imports | {self.summary(st)} | {st['compiles']} compiles, "
            f"{st['wall']:.0f}s (total {time.time() - self.t0:.0f}s)")

    def process(self, D):
        """Return a dict with at least `new`: the file's new import lines."""
        raise NotImplementedError

    def summary(self, st):
        return ""


# --------------------------------------------------------- stage 1a: implied
class Implied(Stage):
    """In file C, `import A` is dropped if another import C -> Y reaches A through
    public non-meta imports, and Y's import is at least as visible as A's."""

    name = "implied"
    compiles = False

    def run(self):
        g = self.g
        before = {m: g.signature(m) for m in g.work}
        plan = {m: g.redundant(m) for m in g.work}
        for m, red in plan.items():  # simulate in memory: nothing visible may change
            g.set_imports(m, [e for e in g.imports(m) if not any(e is x for x in red)])
        bad = [m for m in g.work if g.signature(m) != before[m]]
        if bad:
            sys.exit(f"visible/exported sets would change for: {bad}")
        self.result = {}
        for m in g.work:
            if plan[m]:
                drop = sorted(texts_of(plan[m]))
                new = list(self.meta["orig"][m])
                for t in drop:
                    new.remove(t)
                self.result[m] = dict(old=self.meta["orig"][m], new=new,
                                      removed=[e["mod"] for e in plan[m]])
                say(f"{short(m)}: -{len(plan[m])}  " + " ".join(e["mod"] for e in plan[m]))
        dump(self.result, self.result_path)
        total = sum(len(v) for v in self.meta["orig"].values())
        nred = sum(len(v) for v in plan.values())
        say(f"implied: {nred} of {total} import lines are implied; visible and exported "
            f"module sets checked identical for all {len(g.work)} files")
        say("next: `impmin.py apply implied` (dry run), then with --apply")


# ---------------------------------------------------------- stage 1b: remove
def used_modules(mod):
    """Modules whose constants are referenced by name in `mod` (from its .ilean).
    Only used to decide which dependents to test first."""
    try:
        with open(f"{BUILD_LIB}/{rel(mod)}.ilean") as f:
            data = json.load(f)
    except (OSError, ValueError):
        return frozenset()
    used = set()
    for key in data.get("references", {}):
        try:
            k = json.loads(key)
        except ValueError:
            continue
        c = k.get("c") if isinstance(k, dict) else None
        if isinstance(c, dict) and "m" in c:
            used.add(c["m"])
    return frozenset(used)


class Remove(Stage):
    """An import is removed if the file still compiles without it and every dependent
    still compiles. Nothing is ever added. `meta` and `import all` lines are kept.

    Every file ends up compiled against the final state of what it imports: either
    through an accepted removal, or (if nothing was removed but something it loads
    changed) by recompiling it with its own imports."""

    name = "remove"

    def __init__(self, opts):
        super().__init__(opts)
        self.used = {m: used_modules(m) for m in self.g.work}
        self.idx = {m: i for i, m in enumerate(self.order)}
        self.dep_cache = {}  # (C, visible-tuple) -> result
        # files whose olean in the shadow is not the real build's any more
        self.changed = {D for D, st in self.result.items() if st.get("installed")}

    def vis(self, mod):
        return tuple(self.g.visible(mod, k) for k in ("strict", "meta", "loose"))

    def compile_deps(self, B, deps, predicted):
        """Compile the dependents `deps` (failfast). Returns (failing module, passed)."""
        res = Batch(failfast=True).run(
            [(C, lambda b, C=C: self.compile(C, batch=b, owner=B)) for C in deps])
        fail, passed = None, set()
        for C in deps:
            r = res.get(C)
            if r is None:
                continue
            self.log(ev="dep", B=B, C=C, ok=r["ok"], secs=r["secs"], err=r["err"],
                     predicted=predicted)
            if r["ok"]:
                passed.add(C)
            else:
                fail = fail or C
        if fail is None and len(passed) != len(deps):
            raise RuntimeError("dependents batch incomplete without a failure")
        return fail, passed

    def check_dependents(self, B, deps_before, vis_before):
        """The shadow holds B's candidate olean and self.g reflects it. Compiles the
        dependents whose visible modules changed. Returns (ok, failing, compiled)."""
        pred, rest, compiled = [], [], set()
        for C in deps_before:  # already in topological order
            v = self.vis(C)
            if v == vis_before[C]:
                continue
            key = (C, v)
            if key in self.dep_cache:
                if not self.dep_cache[key]["ok"]:
                    return False, C, compiled
                continue
            used = self.used.get(C, frozenset())  # the root file has no entry
            (pred if used & (vis_before[C][0] - v[0]) else rest).append(C)
        # Predicted failures first, one at a time, so that a hit costs one compile.
        for C in pred:
            r = self.compile(C, owner=B)
            self.dep_cache[(C, self.vis(C))] = r
            self.log(ev="dep", B=B, C=C, ok=r["ok"], secs=r["secs"], err=r["err"],
                     predicted=True)
            if not r["ok"]:
                return False, C, compiled
            compiled.add(C)
        fail, passed = self.compile_deps(B, rest, False)
        for C in passed:
            self.dep_cache[(C, self.vis(C))] = dict(ok=True)
        if fail:
            self.dep_cache[(fail, self.vis(fail))] = dict(ok=False)
            return False, fail, compiled
        return True, None, compiled | passed

    def try_set(self, B, T, deps_before, vis_before, art):
        """Try removing the imports T (subset of self.orig[B]) from B.
        On success the shadow holds B's new olean and self.g reflects it.
        Returns (ok, why, dependents compiled against this olean)."""
        kept = [e for e in self.orig[B] if not any(e is x for x in T)]
        lines = frozenset(e["line"] for e in T)
        if lines in self.local_fail:
            return False, f"{B} itself: {self.local_fail[lines]}", set()
        outdir = art.pop(lines, None)
        if outdir is None:
            r = self.compile(B, texts_of(kept), out=True)
            self.log(ev="local", B=B, drop=[e["mod"] for e in T], ok=r["ok"],
                     secs=r["secs"], err=r["err"])
            if not r["ok"]:
                self.local_fail[lines] = r["err"]
                return False, f"{B} itself: {r['err']}", set()
            outdir = r["outdir"]
        prev_imps = self.g.imports(B)
        bdir = install(B, outdir)
        self.g.set_imports(B, kept)
        ok, failing, compiled = self.check_dependents(B, deps_before, vis_before)
        if ok:
            shutil.rmtree(bdir, ignore_errors=True)
            return True, "dependents compile", compiled
        restore(B, bdir)
        self.g.set_imports(B, prev_imps)
        return False, f"dependent {failing}", set()

    def process(self, B):
        g = self.g
        reset_shadow_module(B)
        self.local_fail = {}  # removed line set -> error, for B itself
        orig = self.orig[B]
        cands = [e for e in orig if not e["all"] and not e["meta"]]
        # The root file loads every file at once, so it also catches clashes between B and
        # files that no work file loads together with B (e.g. auto-named instances).
        deps_before = sorted(g.dependents(B), key=lambda m: self.idx[m]) + [ROOT_MODULE]
        vis_before = {C: self.vis(C) for C in deps_before}
        refresh = bool(self.changed & g.visible(B, "loose"))
        # 1. every import on its own, in parallel; keep the oleans of the successes.
        #    If something B loads changed, B with its own imports is compiled alongside.
        jobs = [(e["line"], lambda b, e=e: self.compile(
            B, [x["text"] for x in orig if x is not e], out=True, batch=b)) for e in cands]
        if refresh:
            jobs.append(("own", lambda b: self.compile(B, out=True, batch=b)))
        res = Batch().run(jobs)
        own = None
        if refresh:
            if not res["own"]["ok"]:
                raise RuntimeError(f"{B} no longer compiles with its own imports against the "
                                   f"processed files: {res['own']['err']}")
            own = res["own"]["outdir"]
        art = {}
        R = []
        for e in cands:
            r = res[e["line"]]
            self.log(ev="single", B=B, drop=e["mod"], ok=r["ok"], secs=r["secs"], err=r["err"])
            if r["ok"]:
                R.append(e)
                art[frozenset([e["line"]])] = r["outdir"]
        say(f"{short(B)}: {len(cands)} imports, {len(deps_before)} dependents; "
            f"removable for the file itself: {len(R)}")
        accepted, compiled = [], set()
        if R:
            ok, why, compiled = self.try_set(B, R, deps_before, vis_before, art)
            say(f"    all {len(R)} together: {'ACCEPTED' if ok else 'rejected'} ({why})")
            if ok:
                accepted = list(R)
            elif len(R) > 1:
                for x in R:
                    ok, why, c = self.try_set(B, accepted + [x], deps_before, vis_before, art)
                    say(f"    {x['mod']}: {'ACCEPTED' if ok else 'rejected'} ({why})")
                    if ok:
                        accepted.append(x)
                        compiled = c
        if accepted:
            # the root file is always checked, the other dependents with FULL_DEPENDENT_CHECK
            rest = [C for C in deps_before if C not in compiled and
                    (FULL_DEPENDENT_CHECK or C == ROOT_MODULE)]
            fail, _ = self.compile_deps(B, rest, None)
            if fail:
                say(f"    final check: dependent {fail} fails; all removals of {short(B)} "
                    "rejected")
                self.log(ev="final-reject", B=B, C=fail)
                accepted = []
                g.set_imports(B, orig)
                if own is None:
                    reset_shadow_module(B)
            elif rest:
                say(f"    final check: the other {len(rest)} dependents compile")
        installed = bool(accepted)
        if not accepted and own is not None:
            shutil.rmtree(install(B, own), ignore_errors=True)
            own, installed = None, True
        for d in list(art.values()) + [own]:
            if d:
                shutil.rmtree(d, ignore_errors=True)
        if installed:
            self.changed.add(B)
        gone = {e["line"] for e in accepted}
        return dict(new=[e["text"] for e in orig if e["line"] not in gone],
                    removed=[e["mod"] for e in accepted], installed=installed)

    def summary(self, st):
        return f"removed {len(st['removed'])}"


# ------------------------------------------------- stages 2 and 3: direct, private
def load_needs(path):
    """From needs.lean output: (needs, namespaces).
    needs: mod -> {used module: dict(weak, pub, wit, pubwit, attr)}. weak: only an
    attribute hint (I line); pub: used in a public signature or exposed body;
    wit/pubwit: shortest (using decl, used decl) pair; attr: attribute witness.
    namespaces: namespace -> modules that register it (N lines)."""
    needs, ns, cur = {}, {}, None
    shorter = lambda w, v: v is None or len(w[0]) + len(w[1]) < len(v[0]) + len(v[1])  # noqa
    with open(path, encoding="utf-8") as f:
        for line in f:
            p = line.rstrip("\n").split("\t")
            if p[0] == "N":
                ns.setdefault(p[1], set()).add(p[2])
                continue
            if p[0] == "M":
                cur = needs.setdefault(p[1], {})
                continue
            d = cur.setdefault(p[1], dict(weak=True, pub=False, wit=None, pubwit=None,
                                          attr=None))
            if p[0] == "C":
                d["weak"] = False
                w = (p[5], p[6])
                if shorter(w, d["wit"]):
                    d["wit"] = w
                if p[2] == "1":
                    d["pub"] = True
                    if shorter(w, d["pubwit"]):
                        d["pubwit"] = w
            elif p[0] == "X":
                d["weak"] = False
                d["pub"] |= p[2] == "1"
            elif p[0] == "I" and d["attr"] is None:
                d["attr"] = ("", "attribute on " + p[2])
    return needs, ns


HINT = re.compile(r"import\s+(?:all\s+)?([^\s`'\"]+)")  # "consider adding `import X`"
UNKNOWN_NS = re.compile(r"unknown namespace `([^`]+)`")


class Refine(Stage):
    """Stages 2 (`direct`) and 3 (`private`); the same search with different settings.

    A file D gets lists `pub` (`public import`) and `priv` (`import`); lines that are
    not touched by the stage (`fixed`) are kept verbatim. The result satisfies:
      * D compiles with exactly these imports;
      * every M in pub fails its test: in `direct`, "M replaced by M's own public
        imports" breaks D; in `private`, "M private, everything below M public" does;
      * every M in priv (only in `private`) fails "M replaced by everything below it,
        private".
    The first guess comes from needs.lean; the compiler corrects it.

    direct:  pub only; private, meta and `import all` imports are fixed.
    private: pub and priv; meta and `import all` imports are fixed.

    Files whose dependencies are all done are processed in parallel (they cannot affect
    each other), so the result is the same as in topological order."""

    reformat = True

    def __init__(self, opts):
        self.name = opts.stage
        self.private = self.name == "private"
        super().__init__(opts)
        g = self.g  # still the original graph: finished files are replayed in run()
        self.avail = frozenset(g.reach("Init") | {"Init"})
        needs_path = self.dir + "/needs.tsv"
        self.needs, self.ns = load_needs(needs_path) if os.path.exists(needs_path) and \
            not opts.no_guess else ({}, {})
        self.pos = g.global_pos()
        self.vold = {m: g.visible(m, "strict") - self.avail for m in g.work}
        work = set(g.work)
        self.deps0 = {m: (g.visible(m, "loose") & work) - {m} for m in g.work}
        # transitive dependents of each file: ready files with more go first (critical path)
        self.ndown = dict.fromkeys(g.work, 0)
        for m in g.work:
            for x in self.deps0[m]:
                self.ndown[x] += 1

    def fresh_start(self):
        if self.opts.no_guess:
            return
        say(f"computing the first guess: lake env lean --run needs.lean {ROOT_MODULE}")
        path = self.dir + "/needs.tsv"
        with open(path + ".tmp", "w") as f:
            subprocess.run(["lake", "env", "lean", "--run", HERE + "/needs.lean", ROOT_MODULE],
                           cwd=ROOT, stdout=f, check=True)
        os.replace(path + ".tmp", path)

    # -- scheduling: independent files in parallel --------------------------------
    def run_files(self, todo):
        done = set(self.result)
        pending = list(todo)
        idx = {D: i for i, D in enumerate(self.order)}
        running = {}
        error = None
        with cf.ThreadPoolExecutor(max_workers=WORKERS) as ex:
            try:
                while pending or running:
                    if error is None:
                        ready = sorted((D for D in pending if self.deps0[D] <= done),
                                       key=lambda D: (-self.ndown[D], idx[D]))
                        for D in ready:
                            if len(running) >= WORKERS:
                                break
                            self.verify_sources()
                            pending.remove(D)
                            running[ex.submit(self.process_counted, D)] = D
                    if not running:
                        break
                    fin, _ = cf.wait(running, return_when=cf.FIRST_COMPLETED)
                    for f in fin:
                        D = running.pop(f)
                        try:
                            st = f.result()
                        except Exception as e:  # let the other files finish, then raise
                            say(f"{short(D)}: FAILED: {e}")
                            error = error or e
                            continue
                        self.finish(D, st)
                        done.add(D)
            except BaseException:
                interrupt_all()
                raise
        if error is not None:
            raise error

    # -- graph helpers -----------------------------------------------------------
    def closure(self, mods):
        r = set(mods)
        for c in mods:
            r |= self.g.reach(c)
        return r

    def antichain(self, mods):
        mods = set(mods)
        return self.topo(x for x in mods
                         if not any(x in self.g.reach(y) for y in mods if y != x))

    def anti_priv(self, priv, pub):
        return self.antichain(set(priv) - self.closure(pub))

    def topo(self, mods):
        return sorted(mods, key=lambda x: self.pos[x])

    def fixed(self, D):
        return [e for e in self.orig[D]
                if e["meta"] or e["all"] or (not self.private and not e["pub"])]

    def bases(self, D):
        """(base_pub, base_all): modules visible anyway through Init and the fixed lines,
        publicly (fixed public lines) and at all (also fixed private lines)."""
        base_pub, base_all = set(self.avail), set(self.avail)
        for e in self.fixed(D):
            if not e["meta"]:
                c = {e["mod"]} | self.g.reach(e["mod"])
                base_all |= c
                if e["pub"]:
                    base_pub |= c
        return base_pub, base_all

    # -- compiling ---------------------------------------------------------------
    def texts(self, D, pub, priv):
        return [f"public import {m}" for m in pub] + [f"import {m}" for m in priv] + \
            texts_of(self.fixed(D))

    @staticmethod
    def lift(pub, extra, priv):
        """(pub + extra, priv) without importing a module both ways: modules of
        `extra` leave `priv` (public includes private visibility)."""
        s = set(extra)
        return pub + list(extra), [m for m in priv if m not in s]

    def trial(self, D, pub, priv, out=False, batch=None):
        return self.compile(D, self.texts(D, pub, priv), out=out, batch=batch)

    def search(self, D, make, n):
        """make(k) -> (pub, priv); make(n) compiles, make(0) does not.
        Parallel bisection; returns k with make(k-1) failing and make(k) compiling."""
        lo, hi = 0, n
        rounds = 0
        while hi - lo > 1:
            w = min(WORKERS, hi - lo - 1)
            pts = sorted({lo + (hi - lo) * (i + 1) // (w + 1) for i in range(w)} - {lo, hi})
            res = Batch().run([(k, lambda b, k=k: self.trial(D, *make(k), batch=b))
                               for k in pts])
            rounds += 1
            passing = [k for k in pts if res[k]["ok"]]
            new_hi = min(passing) if passing else hi
            failing = [k for k in pts if not res[k]["ok"] and k < new_hi]
            lo, hi = (max(failing) if failing else lo), new_hi
        self.log(ev="search", D=D, n=n, k=hi, rounds=rounds)
        return hi

    def hint_pool(self, D, R, err):
        """Small subset of R worth trying before bisecting all of R: modules named in the
        error message and the file's current imports."""
        hinted = set(HINT.findall(err or "")) | {e["mod"] for e in self.orig[D]}
        return [m for m in R if m in hinted]

    def ns_provider(self, R, err):
        """For "unknown namespace `N`" (an `open N`): the first module of R registering N.
        Some such module must be imported, and nothing else is needed for the `open`."""
        for n in UNKNOWN_NS.findall(err or ""):
            mods = self.ns.get(n, ())
            for m in R:
                if m in mods:
                    return m
        return None

    def settle(self, D, level, pub, priv, R, st, failed=None):
        """Add modules of the dependency-ordered list R at `level` ("pub" or "priv")
        until D compiles; (pub + R, priv) resp. (pub, priv + R) must compile.
        `failed`: an already known failing compile of (pub, priv).
        Returns (pub, priv, outdir)."""
        while True:
            if failed is None:
                r = self.trial(D, pub, priv, out=True)
                self.log(ev="try", D=D, pub=pub, priv=priv, ok=r["ok"], secs=r["secs"],
                         err=r["err"])
                if r["ok"]:
                    return pub, priv, r["outdir"]
            else:
                r, failed = failed, None
            if not R:
                raise RuntimeError(f"{D}: does not compile, nothing left to add: {r['err']}")

            def make(k, R):
                return self.lift(pub, R[:k], priv) if level == "pub" else (pub, priv + R[:k])

            x = self.ns_provider(R, r["err"])
            if x is not None:  # no search; (pub + R, priv) still compiles afterwards
                self.log(ev="namespace", D=D, x=x)
                rest = [m for m in R if m != x]
            else:
                pool = self.hint_pool(D, R, r["err"])
                if pool and len(pool) < len(R):
                    ok = self.trial(D, *make(len(pool), pool))["ok"]
                    self.log(ev="pool", D=D, pool=pool, ok=ok)
                    if ok:
                        R = pool
                k = self.search(D, lambda k: make(k, R), len(R))
                x, rest = R[k - 1], R[:k - 1]
            st["found"].append([level, x, r["err"]])
            say(f"      + {'public ' if level == 'pub' else ''}import {x}   ({r['err'][:100]})")
            cov = self.g.reach(x)
            R = [m for m in rest if m not in cov]
            if level == "pub":
                pub = self.antichain(pub + [x])
                priv = self.anti_priv(priv, pub)
            else:
                priv = self.anti_priv(priv + [x], pub)

    def plan(self, level, S, pub, priv, bases):
        """The certification test of the modules S (all at `level`), as (p, q, below):
        the test compiles (p + below, q) resp. (p, q + below); passing means the change
        "(p, q), settled over below" is possible."""
        base_pub, base_all = bases
        below = set()
        for m in S:
            below |= self.g.reach(m)
        if level == "pub":
            rest = [c for c in pub if c not in S]
            q = self.anti_priv(priv + list(S), rest) if self.private else priv
            return rest, q, self.topo(below - self.closure(rest) - base_pub)
        rest = [c for c in priv if c not in S]
        return pub, rest, self.topo(below - self.closure(pub) - self.closure(rest) - base_all)

    def upper(self, level, p, q, below):
        return self.lift(p, below, q) if level == "pub" else (p, q + below)

    # -- one file ----------------------------------------------------------------
    def process(self, D):
        st = dict(found=[], removed=[], demoted=[])
        bases = base_pub, base_all = self.bases(D)
        vold = self.vold[D]
        nd = self.needs.get(D, {})
        strong = {x for x, d in nd.items() if not d["weak"] and x in vold}
        weak = {x for x, d in nd.items() if d["weak"] and x in vold}
        if self.private:
            pub = self.antichain(x for x in strong - base_pub if nd[x]["pub"])
            priv = self.anti_priv(strong - base_all, pub)
        else:  # public unless only used in proofs and visible privately anyway
            pub = self.antichain(x for x in strong - base_pub
                                 if x not in base_all or nd[x]["pub"])
            priv = []
        st["guess"] = dict(pub=pub, priv=priv)
        r = self.trial(D, pub, priv, out=True)
        self.log(ev="guess", D=D, pub=pub, priv=priv, ok=r["ok"], secs=r["secs"], err=r["err"])
        st["guess_ok"] = r["ok"]
        if r["ok"]:
            outdir = r["outdir"]
        else:
            st["guess_err"] = r["err"]
            # keep the guess's split: any module may still be added publicly, so
            # (pub + R, priv) is everything that was visible and compiles
            R = self.topo(vold - self.closure(pub) - base_pub)
            # cheap narrowing: are the attribute hints enough?
            cp = self.closure(pub)
            wk = self.topo(self.closure(weak - cp - base_all) - cp - base_pub)
            if wk:
                ok = self.trial(D, *self.lift(pub, wk, priv))["ok"]
                self.log(ev="narrow", D=D, wk=wk, ok=ok)
                if ok:
                    R = wk
                    st["narrowed"] = True
            pub, priv, outdir = self.settle(D, "pub", pub, priv, R, st, failed=r)
        # certification: every import must fail its test
        cert = set()
        while True:
            todo = [(m, "pub") for m in pub if (m, "pub") not in cert] + \
                   [(m, "priv") for m in priv if (m, "priv") not in cert]
            if not todo:
                break
            plans = {key: self.plan(key[1], [key[0]], pub, priv, bases) for key in todo}
            res = Batch().run([(key, lambda b, key=key: self.trial(
                D, *self.upper(key[1], *plans[key]), batch=b)) for key in todo])
            passing = []
            for key in todo:
                self.log(ev="cert", D=D, M=key[0], level=key[1], needed=not res[key]["ok"],
                         secs=res[key]["secs"], err=res[key]["err"])
                if res[key]["ok"]:
                    passing.append(key)
                else:
                    cert.add(key)
            if not passing:
                break
            # apply all passing tests of one level together (falling back to the first)
            level = "pub" if any(k[1] == "pub" for k in passing) else "priv"
            group = [k[0] for k in passing if k[1] == level]
            shutil.rmtree(outdir, ignore_errors=True)
            p, q, below = self.plan(level, group, pub, priv, bases)
            failed = None
            if len(group) > 1:
                r0 = self.trial(D, p, q, out=True)
                if r0["ok"]:
                    pub, priv, outdir = p, q, r0["outdir"]
                    below = None
                elif self.trial(D, *self.upper(level, p, q, below))["ok"]:
                    failed = r0
                else:
                    group = group[:1]
                    p, q, below = plans[(group[0], level)]
                self.log(ev="cert-group", D=D, level=level, group=group)
            if below is not None:
                pub, priv, outdir = self.settle(D, level, p, q, below, st, failed)
            what = "demoted" if level == "pub" and self.private else "removed"
            for m in group:
                st[what].append(m)
                say(f"      {m}: " + ("public -> private" if what == "demoted" else
                                      "not needed itself, replaced by what is below it"))
        shutil.rmtree(install(D, outdir), ignore_errors=True)

        def why(m):
            d = nd.get(m) or {}
            return (d.get("pubwit") if self.private and m in pub else None) or \
                d.get("wit") or d.get("attr")

        st.update(new=self.texts(D, pub, priv), pub=pub, priv=priv,
                  fixed=texts_of(self.fixed(D)), why={m: why(m) for m in pub + priv})
        return st

    def summary(self, st):
        s = f"{len(st['pub'])} public"
        if self.private:
            s += f" + {len(st['priv'])} private"
        if st["fixed"]:
            s += f" + {len(st['fixed'])} kept"
        s += f" | guess ok: {st['guess_ok']} | found {len(st['found'])}, " \
             f"removed {len(st['removed'])}"
        if self.private:
            s += f", demoted {len(st['demoted'])}"
        return s


# ------------------------------------------------------------- writing sources
def lake_build():
    """Run `lake build` in the project, output shown live; True if it succeeds."""
    refuse_if_unfinished("`lake build`")
    say("lake build")
    t0 = time.time()
    ok = subprocess.run(["lake", "build"], cwd=ROOT).returncode == 0
    say(f"lake build {'succeeded' if ok else 'FAILED'} ({time.time() - t0:.0f}s)")
    return ok


def cmd_apply(stage, do_apply, build):
    """Check every file first; write nothing unless all checks pass."""
    path = stage_dir(stage) + "/result.json"
    res = load_json(path)
    meta = load_json(stage_dir(stage) + "/run.json")
    if res is None or meta is None:
        sys.exit(f"no result for `{stage}`: run `impmin.py run {stage}` first")
    if meta.get("root") != ROOT:
        sys.exit(f"the `{stage}` result was computed for {meta.get('root')}, not {ROOT}")
    final = load_json(stage_dir(stage) + "/final.json")
    if final is not None and not final["ok"]:
        sys.exit(f"the `{stage}` run's final check failed ({ROOT_MODULE} does not compile "
                 f"against the new state): {final['err']}")
    if build and not do_apply:
        sys.exit("--build needs --apply")
    take_lock(f"apply {stage}")
    if build:
        refuse_if_unfinished("apply --build")  # before anything is written
    reformat = stage in ("direct", "private")  # stage 1 only deletes lines
    nwork = len(work_modules())
    unfinished = stage != "implied" and len(res) < nwork
    if unfinished:
        print(f"note: the result covers only {len(res)} of {nwork} files (unfinished run)")
    elif stage != "implied" and final is None:
        print(f"note: {ROOT_MODULE} was not compiled against this result (made by an older "
              f"version without the final check); rely on `lake build`")
    plan, skipped = [], []
    old_total = new_total = 0
    for D, st in sorted(res.items()):
        old_total += len(st["old"])
        new_total += len(st["new"])
        try:
            lines, imps = project_header(D)
            if body_sha(lines, imps) != meta["body"].get(D):
                skipped.append(f"{D}: its non-import lines changed since the run")
                continue
            cur = sorted(texts_of(imps))
            if cur == sorted(st["new"]):
                continue  # nothing to do, or already applied
            if cur != sorted(st["old"]):
                skipped.append(f"{D}: its imports changed since the run")
                continue
            plan.append((D, st, "\n".join(rewrite(lines, imps, st["new"], reformat))))
        except (HeaderError, OSError) as ex:
            skipped.append(f"{D}: {ex}")
    for D, st, _ in plan:
        print(f"{D}: {len(st['old'])} -> {len(st['new'])}")
        for t in sorted(set(st["old"]) - set(st["new"])):
            print("   -", t)
        for t in sorted(set(st["new"]) - set(st["old"])):
            print("   +", t)
    if skipped:
        for s in skipped:
            print("PROBLEM", s)
        sys.exit(f"{len(skipped)} files cannot be applied; nothing was written")
    if do_apply:
        for D, _, text in plan:
            write_atomic(mod_path(D), text)
    print(f"{len(plan)} files {'changed' if do_apply else 'would change'}; "
          f"import lines {old_total} -> {new_total}" + ("" if do_apply else "   (dry run)"))
    if build:
        sys.exit(0 if lake_build() else 1)
    if do_apply and plan:
        if unfinished_run():
            print(f"note: do not run `lake build` until the `{unfinished_run()}` run is "
                  "finished (it uses the shadow tree)")
        else:
            print("next: `lake build` (or use `apply --apply --build`)")


def cmd_format(do_apply):
    """Mathlib-style import blocks (see impgraph.format_block); never changes which
    modules are imported. The root aggregator file is skipped."""
    take_lock("format")
    plan = []
    for mod in work_modules():
        try:
            lines, imps = project_header(mod)
            out = rewrite(lines, imps, texts_of(imps), True)
        except HeaderError as ex:
            print("skipped:", ex)
            continue
        if out != lines:
            plan.append((mod, "\n".join(out)))
    for mod, text in plan:
        if do_apply:
            write_atomic(mod_path(mod), text)
        print("changed:" if do_apply else "would change:", mod_path(mod))
    print(len(plan), "files", "changed" if do_apply else "would change")


def is_import_line(line):
    try:
        parse_line(line)
        return True
    except HeaderError:
        return False


def cmd_verify_diff(table):
    """Check that the working tree differs from HEAD only by deleted import lines
    (meaningful after stage 1 only, before `format`)."""
    bad = 0
    before_total = after_total = 0
    rows = []
    for m in project_modules():
        relp = rel(m) + ".lean"
        old_text = subprocess.run(["git", "show", f"HEAD:{relp}"], cwd=ROOT,
                                  capture_output=True, text=True, check=True).stdout
        old = old_text.split("\n")
        with open(mod_path(m), encoding="utf-8") as f:
            new_text = f.read()
        new = new_text.split("\n")
        j = 0
        deleted = []
        for line in old:
            if j < len(new) and new[j] == line:
                j += 1
            else:
                deleted.append(line)
        if j != len(new):
            print("NOT a pure deletion:", relp)
            bad += 1
            continue
        non_imp = [l for l in deleted if not is_import_line(l)]
        if non_imp:
            print("deleted non-import lines in", relp, non_imp[:3])
            bad += 1
        if m == ROOT_MODULE:
            if deleted:
                print("root file changed!")
                bad += 1
            continue
        nb = len(scan_header(old_text)[1])
        na = len(scan_header(new_text)[1])
        if nb - len(deleted) != na:
            print(f"import counts do not add up in {relp}: {nb} - {len(deleted)} != {na}")
            bad += 1
        before_total += nb
        after_total += na
        rows.append((m, nb, na))
    print(f"imports outside the root file: {before_total} -> {after_total}")
    print("files with 0 imports left:", [m for m, _, a in rows if a == 0])
    if table:
        for m, b, a in rows:
            if a != b:
                print(f"  {b:3d} -> {a:3d}  {m}")
    print("OK" if not bad else f"{bad} PROBLEMS")
    sys.exit(1 if bad else 0)


def cmd_shadow():
    take_lock("shadow")
    refuse_if_unfinished("`shadow`")
    make_shadow("manual")
    say("shadow created at", SHADOW)


# ------------------------------------------------------------------------ main
def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0],
                                 formatter_class=argparse.RawDescriptionHelpFormatter,
                                 epilog="\n".join(__doc__.split("\n")[2:]))
    sub = ap.add_subparsers(dest="cmd", required=True)
    p = sub.add_parser("run", help="run a stage (writes work/STAGE/result.json)")
    p.add_argument("stage", choices=STAGES)
    p.add_argument("--limit", type=int, help="process at most N more files")
    p.add_argument("--fresh", action="store_true",
                   help="discard an unfinished run of this stage instead of resuming it")
    p.add_argument("--no-guess", action="store_true",
                   help="direct/private: start from an empty import list instead of "
                        "needs.lean's guess")
    p = sub.add_parser("apply", help="write a stage's result into the sources")
    p.add_argument("stage", choices=STAGES)
    p.add_argument("--apply", action="store_true", help="really write (default: dry run)")
    p.add_argument("--build", action="store_true",
                   help="with --apply: run `lake build` afterwards to verify the result")
    p = sub.add_parser("format", help="Mathlib-style import blocks")
    p.add_argument("--apply", action="store_true", help="really write (default: dry run)")
    p = sub.add_parser("verify-diff", help="working tree == HEAD minus import lines?")
    p.add_argument("--table", action="store_true")
    sub.add_parser("baseline", help="compile every file once; writes work/base_times.json")
    sub.add_parser("shadow", help="recreate the shadow olean tree")
    sub.add_parser("selftest", help="check that oleans installed in the shadow are used")
    a = ap.parse_args()
    try:
        if a.cmd == "run":
            cls = {"implied": Implied, "remove": Remove, "direct": Refine, "private": Refine}
            cls[a.stage](a).run()
        elif a.cmd == "apply":
            cmd_apply(a.stage, a.apply, a.build)
        elif a.cmd == "format":
            cmd_format(a.apply)
        elif a.cmd == "verify-diff":
            cmd_verify_diff(a.table)
        elif a.cmd == "baseline":
            cmd_baseline()
        elif a.cmd == "shadow":
            cmd_shadow()
        elif a.cmd == "selftest":
            cmd_selftest()
    except (KeyboardInterrupt, Interrupted):
        interrupt_all()
        say("interrupted; nothing half-done was recorded (`run` resumes where it stopped)")
        sys.exit(130)


if __name__ == "__main__":
    main()
