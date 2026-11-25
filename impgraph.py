"""Project settings, import-header parsing and the import graph.

Only reads files, except for `write_atomic`; the callers decide what to write.
"""
import glob
import hashlib
import os
import re
import stat
import subprocess
import threading

# --------------------------------------------------------------------- settings
# The project: `--project` / IMPMIN_ROOT, default the current directory. The root module
# (the file that imports all others; never touched): `--root-module` / IMPMIN_MODULE,
# default inferred by `_root_module`. The -D options are read per file from Lake's
# .setup.json files (see impmin.py), so the lakefile needs no copy here.
ROOT = os.path.abspath(os.environ.get("IMPMIN_ROOT") or os.getcwd())
if not os.path.isfile(os.path.join(ROOT, "lean-toolchain")):
    raise SystemExit(f"{ROOT} is not a Lean project (no lean-toolchain file); "
                     "run from the project directory or pass --project PATH")


def _tracked_lean_files():
    out = subprocess.run(["git", "ls-files", "*.lean"], cwd=ROOT, capture_output=True,
                         text=True)
    if out.returncode != 0:
        raise SystemExit(f"{ROOT} is not a git repository: {out.stderr.strip()}")
    return [f for f in out.stdout.split("\n") if f.endswith(".lean")]


def _root_module():
    """IMPMIN_MODULE, else the top-level `X.lean` with a directory `X/` of tracked files;
    if there are several, the one the lakefile names as default target."""
    if os.environ.get("IMPMIN_MODULE"):
        return os.environ["IMPMIN_MODULE"]
    files = _tracked_lean_files()
    cands = sorted(f[:-5] for f in files if "/" not in f and
                   any(g.startswith(f[:-5] + "/") for g in files))
    if len(cands) == 1:
        return cands[0]
    defaults = set()
    for name, pat in (("lakefile.toml", r"defaultTargets\s*=\s*\[([^\]]*)\]"),
                      ("lakefile.lean", r"@\[default_target\]\s*lean_lib\s+«?([\w.]+)»?")):
        p = os.path.join(ROOT, name)
        if os.path.isfile(p):
            with open(p, encoding="utf-8") as f:
                for m in re.findall(pat, f.read()):
                    defaults |= set(re.findall(r"[\w.]+", m))
    pick = [c for c in cands if c in defaults]
    if len(pick) == 1:
        return pick[0]
    raise SystemExit(f"cannot tell the root module of {ROOT} (candidates: {cands}); "
                     "pass --root-module NAME")


ROOT_MODULE = _root_module()


def _toolchain_dir():
    """elan's directory for the toolchain named in ROOT/lean-toolchain."""
    with open(os.path.join(ROOT, "lean-toolchain")) as f:
        name = f.read().strip()
    d = os.path.expanduser("~/.elan/toolchains/" + name.replace("/", "--").replace(":", "---"))
    if not os.path.isdir(d):
        raise RuntimeError(f"toolchain {name} not found at {d}")
    return d


TOOLCHAIN = _toolchain_dir()
LEAN = TOOLCHAIN + "/bin/lean"
TC = TOOLCHAIN + "/src/lean"  # sources of Init, Lean, Std, Lake
SRC_ROOTS = [ROOT] + sorted(glob.glob(ROOT + "/.lake/packages/*")) + [TC, TC + "/lake"]


class HeaderError(Exception):
    """An import header the scripts cannot handle safely."""


# ---------------------------------------------------------------------- parsing
_KEYWORDS = ("module", "prelude", "public", "meta", "import", "all")


def _lex(s, flags):
    """Tokens of Lean source `s` as (text, line), skipping comments. Only meant for the
    header: a token is a maximal run of non-space characters outside comments (with
    «...» kept whole). Sets flags["unclosed"] if a block comment never closes."""
    i, n, line = 0, len(s), 1
    while i < n:
        c = s[i]
        if c == "\n":
            line += 1
            i += 1
        elif c.isspace():
            i += 1
        elif s.startswith("--", i):
            j = s.find("\n", i)
            i = n if j < 0 else j
        elif s.startswith("/-", i):
            depth, i = 1, i + 2
            while i < n and depth:
                if s.startswith("/-", i):
                    depth += 1
                    i += 2
                elif s.startswith("-/", i):
                    depth -= 1
                    i += 2
                else:
                    line += s[i] == "\n"
                    i += 1
            if depth:
                flags["unclosed"] = True
        else:
            j = i
            while j < n and not s[j].isspace() and not s.startswith("--", j) and \
                    not s.startswith("/-", j):
                if s[j] == "«":
                    k = s.find("»", j)
                    j = n if k < 0 else k + 1
                else:
                    j += 1
            yield s[i:j], line
            i = j


def _import_cmd(words):
    """'done' / 'prefix' / None: is `words` a whole import command, a prefix of one, or
    neither. Grammar: [public] [meta] import [all] <module>."""
    i = 0
    for kw in ("public", "meta"):
        if i < len(words) and words[i] == kw:
            i += 1
    if i == len(words):
        return "prefix"
    if words[i] != "import":
        return None
    i += 1
    if i < len(words) and words[i] == "all":
        i += 1
    if i == len(words):
        return "prefix"
    if words[i] in _KEYWORDS or i + 1 != len(words):
        return None
    return "done"


def scan_header(s):
    """(is_module, [import dicts], rest) for Lean source `s`; rest is (token, line) of the
    first token after the header, or None. Import dict: pub, meta, all, mod, line (of the
    command's first token), end (line of the module name)."""
    flags = {}
    is_mod = False
    imps = []
    pend = []
    for tok, line in _lex(s, flags):
        pend.append((tok, line))
        words = [t for t, _ in pend]
        if not imps and not is_mod and words == ["module"]:
            is_mod, pend = True, []
            continue
        if not imps and words == ["prelude"]:
            pend = []
            continue
        kind = _import_cmd(words)
        if kind == "prefix":
            continue
        if kind == "done":
            imps.append(dict(pub=words[0] == "public", meta="meta" in words[:2],
                             all=words[-2] == "all", mod=words[-1], line=pend[0][1],
                             end=pend[-1][1]))
            pend = []
            continue
        return is_mod, imps, pend[0]
    if flags.get("unclosed"):
        return is_mod, imps, ("/-", 0)
    return is_mod, imps, (pend[0] if pend else None)


def read_header(path):
    """(lines, is_module, [import dicts]) of a source file. Each import dict also gets
    `text`: its line, stripped (with any trailing comment)."""
    with open(path, encoding="utf-8") as f:
        s = f.read()
    is_mod, imps, _ = scan_header(s)
    lines = s.split("\n")
    for e in imps:
        e["text"] = lines[e["line"] - 1].strip()
        e["keep"] = KEEP in e["text"]
    return lines, is_mod, imps


# lake shake's annotations (only the comments are read; lake shake itself is never used):
#   import X -- shake: keep             this import line is never changed
#   module -- shake: keep-all           no import of this file is changed or removed
#   module -- shake: keep-downstream    every file that reaches this module keeps reaching it
KEEP = "shake: keep"


def file_flags(path):
    """keep_all / keep_down from the comment on the `module` line, and imports_only:
    nothing but comments after the import block (a file that only re-exports)."""
    with open(path, encoding="utf-8") as f:
        s = f.read()
    _, _, rest = scan_header(s)
    first = next(_lex(s, {}), None)
    line = s.split("\n")[first[1] - 1] if first and first[0] == "module" else ""
    return dict(keep_all="shake: keep-all" in line,
                keep_down="shake: keep-downstream" in line, imports_only=rest is None)


def parse_header(path):
    """(is_module, [import dicts]) of a source file."""
    _, is_mod, imps = read_header(path)
    return is_mod, imps


def parse_line(text):
    """Import dict of one import line (as stored in results); HeaderError otherwise."""
    is_mod, imps, rest = scan_header(text)
    if is_mod or len(imps) != 1 or rest is not None:
        raise HeaderError(f"not a single import line: {text!r}")
    e = imps[0]
    e["line"] = e["end"] = 0
    e["text"] = text.strip()
    e["keep"] = KEEP in e["text"]
    return e


def check_layout(path, lines, imps):
    """Every import must be alone on its own line (comments allowed if they close on the
    same line), so that lines can be deleted and rewritten one by one."""
    seen = set()
    for e in imps:
        ln = e["line"]
        if e["end"] != ln:
            raise HeaderError(f"{path}:{ln}: import split over several lines")
        if ln in seen:
            raise HeaderError(f"{path}:{ln}: several imports on one line")
        seen.add(ln)
        try:
            parse_line(lines[ln - 1])
        except HeaderError:
            raise HeaderError(f"{path}:{ln}: import line with other content or an open "
                              f"block comment: {lines[ln - 1].strip()!r}") from None


def project_header(mod):
    """(lines, [import dicts]) of a project file, with the layout checked."""
    path = mod_path(mod)
    lines, _, imps = read_header(path)
    check_layout(path, lines, imps)
    return lines, imps


_MODULE_LINE = re.compile(r"^module\s*(--.*)?$")


def body_sha(lines, imps):
    """Hash of everything except the import lines, blank lines and a comment on the
    `module` line (where the shake annotations go)."""
    drop = {e["line"] - 1 for e in imps}
    body = "\n".join("module" if _MODULE_LINE.match(l) else l
                     for i, l in enumerate(lines) if i not in drop and l.strip())
    return hashlib.sha256(body.encode()).hexdigest()


def project_modules():
    """Tracked .lean files of the project that belong to ROOT_MODULE's namespace."""
    mods = (f[:-5].replace("/", ".") for f in _tracked_lean_files())
    return sorted(m for m in mods if m == ROOT_MODULE or m.startswith(ROOT_MODULE + "."))


def work_modules():
    """Project modules except the root aggregator file: the files the stages process."""
    return [m for m in project_modules() if m != ROOT_MODULE]


def find_source(mod):
    rel = mod.replace(".", "/") + ".lean"
    for r in SRC_ROOTS:
        p = os.path.join(r, rel)
        if os.path.isfile(p):
            return p
    return None


def mod_path(mod):
    return os.path.join(ROOT, mod.replace(".", "/") + ".lean")


def short(mod):
    """Module name without the root prefix, for progress lines."""
    p = ROOT_MODULE + "."
    return mod[len(p):] if mod.startswith(p) else mod


# ------------------------------------------------------------------------ graph
class Graph:
    """Import graph of the project plus everything it transitively imports
    (including `Init`, which every non-prelude file imports implicitly).

    Thread-safe: every read and `set_imports` holds one lock. Only project modules can
    change, so caches of other modules are never invalidated."""

    def __init__(self):
        self.proj = project_modules()
        self.projset = frozenset(self.proj)
        self.work = [m for m in self.proj if m != ROOT_MODULE]
        self.G = {}  # mod -> (is_module, imports)
        self._memo = {}  # (mod, kind) -> frozenset: reach
        self._vis = {}  # (mod, kind) -> frozenset: visible
        self._lock = threading.RLock()
        self._load(list(self.proj) + ["Init"])
        lost = [m for m in self.work if m not in self.reach(ROOT_MODULE, "loose")]
        if lost:
            raise RuntimeError(f"not imported by {ROOT_MODULE} (so `lake build` would not "
                               f"check them): {lost}")

    def _load(self, stack):
        while stack:
            m = stack.pop()
            if m in self.G:
                continue
            p = find_source(m)
            if p is None:
                raise RuntimeError(f"cannot resolve module {m}")
            self.G[m] = parse_header(p)
            stack.extend(e["mod"] for e in self.G[m][1])

    def set_imports(self, mod, imps):
        assert mod in self.projset, mod
        with self._lock:
            self._load([e["mod"] for e in imps])
            self.G[mod] = (self.G[mod][0], imps)
            self._memo = {k: v for k, v in self._memo.items() if k[0] not in self.projset}
            self._vis = {}

    def imports(self, mod):
        return self.G[mod][1]

    # --- reachability under three notions of "follows this edge" ---------------
    # strict: public non-meta edges (what an importer can actually see)
    # meta:   public edges including meta
    # loose:  every edge (what gets loaded at all)
    @staticmethod
    def _follows(kind, is_mod, e):
        if kind == "loose":
            return True
        if is_mod and not e["pub"]:
            return False
        if kind == "strict" and e["meta"]:
            return False
        return True

    def reach(self, mod, kind="strict"):
        """Modules re-exported by `mod` under `kind` (excluding `mod` itself)."""
        with self._lock:
            memo = self._memo
            if (mod, kind) in memo:
                return memo[(mod, kind)]
            stack = [mod]
            while stack:  # iterative post-order: no recursion limit, safe in threads
                m = stack[-1]
                if (m, kind) in memo:
                    stack.pop()
                    continue
                is_mod, imps = self.G[m]
                kids = [e["mod"] for e in imps if self._follows(kind, is_mod, e)]
                missing = [c for c in kids if (c, kind) not in memo]
                if missing:
                    stack.extend(missing)
                    continue
                r = set(kids)
                for c in kids:
                    r |= memo[(c, kind)]
                memo[(m, kind)] = frozenset(r)
                stack.pop()
            return memo[(mod, kind)]

    def visible(self, mod, kind):
        """Modules visible inside `mod`: first hop follows every import of the
        right phase, later hops follow re-exports only."""
        with self._lock:
            key = (mod, kind)
            if key not in self._vis:
                r = set()
                for e in self.G[mod][1]:
                    if kind == "strict" and e["meta"]:
                        continue
                    r.add(e["mod"])
                    r |= self.reach(e["mod"], kind)
                self._vis[key] = frozenset(r)
            return self._vis[key]

    def signature(self, mod):
        """Everything about `mod`'s view of the world that an import edit can change."""
        return tuple(self.visible(mod, k) for k in ("strict", "meta", "loose")) + \
            tuple(self.reach(mod, k) for k in ("strict", "meta"))

    def dependents(self, mod):
        """Project modules that load `mod` (any edge kind)."""
        return [m for m in self.work if m != mod and mod in self.visible(m, "loose")]

    def topo_order(self):
        """Project modules, dependencies first; ties: fewest dependents first."""
        P = set(self.work)
        deps = {m: {e["mod"] for e in self.imports(m) if e["mod"] in P} for m in self.work}
        ndep = dict.fromkeys(self.work, 0)
        for m in self.work:
            for x in self.visible(m, "loose") & P:
                ndep[x] += 1
        order = []
        done = set()
        remaining = set(self.work)
        while remaining:
            ready = sorted((m for m in remaining if deps[m] <= done),
                           key=lambda m: (ndep[m], m))
            if not ready:
                raise RuntimeError("import cycle")
            order.extend(ready)
            done.update(ready)
            remaining.difference_update(ready)
        return order

    def global_pos(self):
        """Position of every module in one fixed topological order (dependencies first)."""
        pos = {}
        seen = set()
        for root in sorted(self.G):
            if root in seen:
                continue
            seen.add(root)
            stack = [(root, iter([e["mod"] for e in self.G[root][1]]))]
            while stack:
                node, it = stack[-1]
                for c in it:
                    if c not in seen:
                        seen.add(c)
                        stack.append((c, iter([e["mod"] for e in self.G[c][1]])))
                        break
                else:
                    pos[node] = len(pos)
                    stack.pop()
        return pos

    def redundant(self, mod):
        """Imports of `mod` implied by another import of `mod` (stage 1a rule); lines
        marked `shake: keep` are never dropped."""
        _, imps = self.G[mod]
        out = []
        for e in imps:
            if e["meta"] or e["all"] or e["keep"]:
                continue
            for y in imps:
                if y is e or y["meta"] or y["all"] or y["mod"] == e["mod"]:
                    continue
                if e["pub"] and not y["pub"]:
                    continue
                if e["mod"] in self.reach(y["mod"], "strict"):
                    out.append(e)
                    break
        return out


# --------------------------------------------------------------------- writing
def format_block(texts):
    """Import lines in Mathlib order: public meta, public, blank, meta, plain; each
    sorted by module name in code-point order (the order `lake exe mk_all` uses)."""
    groups = {}
    for t in texts:
        e = parse_line(t)
        groups.setdefault((e["pub"], e["meta"]), []).append((e["mod"], e["text"]))
    get = lambda k: [t for _, t in sorted(groups.get(k, []))]  # noqa: E731
    pub = get((True, True)) + get((True, False))
    priv = get((False, True)) + get((False, False))
    return pub + ([""] if pub and priv else []) + priv


def rewrite(lines, imps, new, reformat):
    """`lines` with the import lines `imps` replaced by the import lines `new`.

    reformat=False: `new` must be a subset of the current lines; the others are deleted
    in place and nothing else moves. reformat=True: the block is rewritten by
    `format_block` with one blank line before and after. Trials and `apply` both use
    this, so a trial compiles exactly what `apply` writes."""
    idx = [e["line"] - 1 for e in imps]
    if not idx:
        if new:
            raise HeaderError("cannot add imports to a file without any")
        return list(lines)
    if not reformat:
        keep = list(new)
        drop = set()
        for i in idx:
            t = lines[i].strip()
            if t in keep:
                keep.remove(t)
            else:
                drop.add(i)
        if keep:
            raise HeaderError(f"not a pure deletion: {keep}")
        return [l for i, l in enumerate(lines) if i not in drop]
    lo, hi = min(idx), max(idx)
    inner = [lines[i] for i in range(lo, hi + 1) if i not in idx and lines[i].strip()]
    if inner:
        raise HeaderError(f"non-import line inside the import block: {inner[0].strip()!r}")
    before, after = lines[:lo], lines[hi + 1:]
    while before and not before[-1].strip():
        before.pop()
    while after and not after[0].strip():
        after.pop(0)
    return before + [""] + format_block(new) + [""] + after


def new_source(mod, new, reformat):
    """Source text of project file `mod` with its import block replaced by `new`."""
    lines, imps = project_header(mod)
    return "\n".join(rewrite(lines, imps, new, reformat))


def write_atomic(path, text):
    """Write via a temporary file and rename, so an interrupt never truncates `path`.
    The permission bits of an existing `path` are kept (git tracks the executable bit)."""
    tmp = path + ".impmin-tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        f.write(text)
        f.flush()
        os.fsync(f.fileno())
    if os.path.exists(path):
        os.chmod(tmp, stat.S_IMODE(os.stat(path).st_mode))
    os.replace(tmp, path)
