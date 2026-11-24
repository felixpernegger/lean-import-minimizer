# Lean import minimiser

Scripts that minimise the imports of a Lean 4 project that uses the module system
(`module` files with `public import` / `import`), without `lake shake`. The compiler
decides every change: an import is removed, replaced or made private only after a compile
of the affected file shows that it still works.

They were written for and run on
[Sphere-Packing-Lean](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean)
(Lean v4.36.0, 72 files below the root file) in November 2026. Nothing here is packaged:
the project path, root module and `-D` options are hardcoded (see
[Hardcoded settings](#hardcoded-settings)) and the scripts were only ever run on that one
project.

There is one entry point, `impmin.py`. Every stage is run the same way:

- `impmin.py run STAGE` decides the new import lists and writes them to
  `work/STAGE/result.json`. It never edits the sources.
- `impmin.py apply STAGE` shows what would change in the sources; with `--apply` it
  writes it, and with `--apply --build` it then runs `lake build` to verify it.

## What the stages do

| Stage | `STAGE` | Rule | Result on Sphere-Packing |
|---|---|---|---|
| 1a. Implied imports | `implied` | Delete imports implied by another import of the same file (graph only, no compiling). | 265 → 162 import lines |
| 1b. Removal | `remove` | Delete every import that the file and all its dependents compile without. | 162 → 133 |
| 2. Direct imports | `direct` | Every import must itself provide something the file uses; pass-through imports are replaced by the modules actually used. | 133 → 157 |
| 3. Privatisation | `private` | Every import gets the weakest modifier that compiles: `import` unless the file needs `public import`. | 157 → 243 (114 public, 128 private, 1 public meta) |

The results column comes from the runs recorded in `runs-sphere-packing/`, made with an
earlier version of the scripts (see the end of this file).

Stages 1a and 1b only delete lines, and `apply` deletes them in place. Stages 2 and 3 are
the same algorithm with different settings (see below), and `apply` rewrites the import
block in Mathlib order. `impmin.py format` sorts and spaces import blocks the Mathlib way
without changing which modules are imported.

The numbers go up in stages 2 and 3 on purpose: a file that used to get a module through
another file's re-export now names it itself.

`meta` imports, `import all` imports and the root aggregator file are never changed by any
stage. The root file must keep listing every module for `lake exe mk_all --check --module`.

### Exact definitions

**Stage 1a, implied imports** (`implied`). In file `C`, `import A` is dropped if
another import `C → Y` reaches `A` through a chain of `public`, non-`meta` imports, and
`Y`'s import is at least as visible as `A`'s. `meta` and `import all` lines are never
dropped and never used as providers. The stage checks that every file sees and re-exports
exactly the same set of modules before and after.

**Stage 1b, individual removal** (`remove`). An import (not `meta`, not `import all`) is
removed if the file still compiles without it *and* every dependent still compiles. No
import is ever added to a dependent, so a removal that breaks a dependent is rejected.
Dependents whose visible modules change are compiled for every candidate; once a file's
removals are decided, all its other dependents are compiled once more against its new
olean (`FULL_DEPENDENT_CHECK` in `impmin.py`), because they load that olean too. If one of
them fails, all removals of that file are rejected. The root file counts as a dependent of
every file and is compiled at that point in any case: it is the only module that loads all
files together, so it catches clashes that no single file sees (for example, after an
import is removed, an auto-named instance `instFoo_1` becomes `instFoo` and collides with
the `instFoo` of a module it no longer imports).

**Stage 2, direct imports** (`direct`). For a file `D` with import list `C`:
1. `D` compiles with exactly the imports `C`.
2. For every `M` in `C`, replacing `M` by `M`'s own public imports breaks `D`.
3. Imports implied by another import of `D` (through public chains) stay omitted.

**Stage 3, privatisation** (`private`). For a file `D` with lists `pub` and `priv`:
1. `D` compiles with `public import` for `pub` and `import` for `priv`.
2. For every `M` in `pub`: "`M` private, everything below `M` public" breaks `D`.
3. For every `M` in `priv`: "`M` replaced by everything below it, private" breaks `D`.

Where a file needs `M` only in proofs but something beneath `M` in statements, the result
is `import M` plus a `public import` of the lower module.

Stages 2 and 3 are one class (`impmin.py: Refine`) with these settings:

| | `direct` | `private` |
|---|---|---|
| Lists that are optimised | `pub` | `pub` and `priv` |
| Lines kept verbatim | `meta`, `import all`, private imports | `meta`, `import all` |
| Test for `M` in `pub` | removal: `M` replaced by its own public imports | demotion: `M` private, everything below `M` public |
| Test for `M` in `priv` | (none) | removal: `M` replaced by everything below it, private |
| First guess | modules used (unless only used in proofs and already visible through a kept private import) | modules used; public if used in a public signature or exposed body |

A module that a kept line makes visible is not imported again, with one distinction: a
kept *private* line provides only private visibility, so a module it reaches can still be
added as a `public import` when the file needs it in a statement.

Certification runs all tests of the current lists in parallel. All passing tests of one
level are applied together (one compile checks the combination; if it fails, only the
first is applied), then the remaining tests are run again on the new lists.

## How it avoids rebuilds

Lake rebuilds every dependent of a changed file, also when the change is reverted. One
trial on a file with 37 dependents cost about 150 s through Lake against about 2 s here.
So Lake is used only for a baseline build and a final verification build. In between:

- **Direct `lean` calls.** `run_lean` runs
  `lean -R <src root> <file> --json -D<options>` with the environment from
  `lake env env`, and kills the process at the first JSON message with severity `error`.
  `lean` is started through `stdbuf -oL`: on a pipe its output is otherwise block-buffered,
  and the first error would only arrive when the compile has finished anyway.
  Only such a message counts as "does not compile". A compile that ends without one
  (timeout, killed by a signal such as the OOM killer, a crash, non-JSON output) is retried
  once with twice the time; if that fails too, the run stops with an error rather than
  record a decision (it can be resumed). Timeouts are 3 × the baseline time + 90 s.
- **Temporary sources.** A trial compiles a temporary copy of the file with a different
  import block, rewritten by the same function `apply` uses (`impgraph.rewrite`), so the
  run compiles exactly the text `apply` will write. The real sources are edited only by
  `apply`.
- **Shadow olean tree.** At the start of a run, `<repo>/.lake/import-min/lean` is created
  as a hardlink copy of `.lake/build/lib/lean` and put into `LEAN_PATH` in place of the
  real build directory. When a file is done, its recompiled olean is installed there by
  rename, so later files are compiled against the new version while Lake's real build
  stays untouched and up to date. Stage 1b also installs each candidate's olean while its
  dependents are tested, and puts the previous one back if the candidate is rejected. The
  file `.lake/import-min/owner` records which stage's run the shadow belongs to; it is
  removed before the shadow is recreated and written only after the copy succeeded. A run
  resumes only with its own shadow.
- **Dependencies first.** Files are processed in topological order, so everything a file
  imports is final, as an import list and as an olean, when the file is processed. In
  stage 1b a file from which nothing is removed is recompiled with its own imports when
  something it loads has changed, so its olean in the shadow is current too. Stages 2 and
  3 process files in parallel once all the files they load are done, starting the ready
  files with the most (transitive) dependents first, since they head the longest chains;
  files that run at the same time cannot affect each other, so the result is the same as in
  strict order. Stage 1b is sequential (its candidate oleans are in the shared shadow).
- **Final check.** When all files of a stage are done, the root file is compiled against
  the final shadow, which by then holds every file's new olean built in dependency order.
  The outcome is recorded in `work/STAGE/final.json`; if it fails, the run exits non-zero
  and `apply` refuses the result.
- **One process at a time.** Every command that uses the shadow or edits sources (`run`,
  `apply`, `format`, `shadow`, `selftest`) holds a lock on `.lake/import-min/lock`.
  Temporary sources, compile outputs and backups go to `.lake/import-min/tmp` (on the
  same filesystem as the shadow, so installing is a rename).

### The search used in stages 2 and 3

When a candidate import list does not compile, the missing module is found by compiling:
all modules the file could see originally are put in dependency order, and a parallel
bisection finds the shortest prefix that makes the file compile. The last module of that
prefix is needed itself. This costs about 4 rounds of 4 compiles per missing module
(`Refine.search`). It assumes that adding imports never breaks a file.

Before bisecting everything, cheaper candidates are tried; each is still confirmed by
compiling:
- If the error is `unknown namespace N` (an `open N`), a module that registers `N`
  (from `needs.lean`) is added directly: some such module has to be imported and nothing
  else is needed for the `open`.
- If the modules named in the error message and the file's current imports together make
  the file compile, the bisection runs over these few modules only.
- After a failed first guess, the same check is made with the modules that put
  attributes on declarations the file uses (`I` lines below).

### The first guess (`needs.lean`)

To avoid running that search for every import, `needs.lean` loads the built project once
and prints, per file, the modules whose declarations occur in the file's compiled terms,
plus the module uses Lean records while elaborating (notation, tactics, attributes; see
`Lean/ExtraModUses.lean`), with a flag saying whether the use is in a public signature or
exposed body. This is the same raw data `lake shake` reads. It also prints the modules
that put attributes on used declarations (a weak hint, `I` lines) and, for every loaded
module, the namespaces it registers (`N` lines). `run direct` and `run private` run it
themselves at the start, so it always describes the current state. It is only a starting
point: on Sphere-Packing the guess compiled for 63 of 72 files in stage 2 and 61 of 72 in
stage 3, and the search plus the certification compiles corrected the rest. When the
guess fails, its public/private split is kept and only the missing modules are searched.

## Files

| File | Purpose |
|---|---|
| `impmin.py` | The entry point: compile helpers (`run_lean`, `compile_mod`, `Batch`), shadow tree and lock, the stage driver (`Stage`) and the stages `Implied`, `Remove`, `Refine` (`direct` and `private`), plus `apply`, `format`, `verify-diff`, `baseline`, `shadow`, `selftest`. |
| `impgraph.py` | Settings; parses import headers (a small tokenizer that skips comments) of the project and of everything it imports; reachability under three notions of visibility (`strict` = public non-meta chains, `meta`, `loose`); topological order; rewriting import blocks. |
| `needs.lean` | First-guess extraction, run by `impmin.py` with `lake env lean --run`. |
| `runs-sphere-packing/` | Logs and results of the Sphere-Packing runs (see below). |

Working files go to `work/` next to the scripts:

| Path | Content |
|---|---|
| `work/base_times.json` | Project path and per-file compile time, peak memory and success of the baseline. |
| `work/STAGE/run.json` | Written at a fresh start: project path, git commit, the original import lines of every file and a hash of the rest of each file. |
| `work/STAGE/result.json` | Per file: `old` and `new` import lines and statistics; rewritten after every file. |
| `work/STAGE/log.jsonl` | Every compile and search step. |
| `work/STAGE/progress.out` | The progress lines printed on the terminal. |
| `work/STAGE/needs.tsv` | `direct`/`private`: output of `needs.lean`. |
| `work/STAGE/final.json` | Outcome of the final check (root file compiled against the finished run). |

## Running it

Run from anywhere, with `T` set to this folder. The project must be on a clean git state
so that every stage can be reviewed with `git diff` and undone with `git checkout`.

```bash
python3 $T/impmin.py run implied              # 1a: instant, graph only
python3 $T/impmin.py apply implied            # dry run; then again with --apply
python3 $T/impmin.py apply implied --apply --build

python3 $T/impmin.py run remove               # 1b
python3 $T/impmin.py apply remove --apply --build
python3 $T/impmin.py verify-diff --table      # HEAD minus import lines only?
python3 $T/impmin.py format --apply           # Mathlib-style blocks

python3 $T/impmin.py run direct               # 2
python3 $T/impmin.py apply direct --apply --build

python3 $T/impmin.py run private              # 3
python3 $T/impmin.py apply private --apply --build

lake exe mk_all --check --module
rm -rf .lake/import-min
```

A build after each `apply` is required, for two reasons. A fresh `run` (except `implied`)
refuses to start unless `lake build --no-build` succeeds, because the shadow tree is
copied from the build. And the final `lake build` is the only check of the whole
project in its real build order: a run compiles each file against its final imports, but
not every file in every combination. With `--build`, `apply` runs it and exits non-zero
if it fails; without `--build`, run `lake build` yourself (for example to look at the diff
first). `--build` refuses to run while an unfinished run's shadow tree exists (`lake build`
must not run during a run).

What `run STAGE` does on a fresh start: refuses if another stage's unfinished run owns
the shadow tree, checks the build, records `run.json`, checks `OPTS` against Lake's
options, runs `baseline` if `work/base_times.json` has no successful entry for some file,
runs `needs.lean` (`direct`/`private`), creates the shadow tree, then processes the files.

Options of `run`:

| Option | Effect |
|---|---|
| `--limit N` | Process at most N more files, then stop (the run can be resumed). |
| `--fresh` | Discard an unfinished run of this stage and start over. |
| `--no-guess` | `direct`/`private`: ignore `needs.lean` and find every import by the search (slow; for measuring how much the guess saves). |

**Resuming.** If `work/STAGE/result.json` exists, `run STAGE` continues with the first
unfinished file. This needs the shadow tree of the interrupted run; if it is gone or
belongs to another run, start over with `--fresh`. Ctrl-C stops all compiles at once and
records nothing half-done. Before every file the sources are checked against `run.json`:
unfinished files must have their original imports, finished files their original or
their new imports, and no file may have changed outside its import lines. So `apply` on
an unfinished result (it applies the finished files and says so) can be followed by
resuming the run; the graph is always rebuilt from the original import lines, so the
resumed run decides as an uninterrupted one would.

**Safety of `apply`.** Every file is checked before anything is written: its import
lines must be exactly the `old` lines of the result (or already the `new` ones), the rest
of the file must be unchanged since the run started, and the result must belong to this
project. If any file fails a check, nothing is written. A result whose final check failed
is refused. Files are written via a temporary file and rename, keeping their permission
bits (git tracks the executable bit). Running `apply` twice does nothing the second time.

**Unsupported headers.** An import must be alone on its line (a trailing comment is fine).
For `direct`/`private` and `format`, the import block may contain blank lines but no
comment lines. A fresh `run` lists every file that breaks these rules and stops.

Other commands: `baseline` (compile every file once against the real build),
`shadow` (recreate the shadow by hand), `selftest` (checks on two small files that an
olean installed in the shadow is the one dependents load, and that the real build is
untouched). Both `shadow` and `selftest` refuse to touch the shadow of an unfinished run.

Setting `IMPMIN_WORKERS` controls how many `lean` processes run at once, over all files
(default 4; 4 was safe with about 6 GB of free RAM).

## Hardcoded settings

All in the settings block at the top of `impgraph.py`. Change them before using the
scripts on another project.

| Setting | What |
|---|---|
| `ROOT` | Absolute path of the project; can be overridden with the environment variable `IMPMIN_ROOT`. |
| `ROOT_MODULE` | Name of the aggregator file that is never touched (`SpherePacking`). Only tracked files in its namespace are processed, and each of them must be imported (transitively) by it. |
| `OPTS` | The `-D` options Lake would pass; must mirror `leanOptions` in the lakefile. A fresh run compares them with the options in Lake's `.lake/build/ir/*.setup.json` and stops if they differ. |

The toolchain (the `lean` binary and the `Init`/`Lean`/`Std`/`Lake` sources) is found from
`ROOT/lean-toolchain` in `~/.elan/toolchains`. The file list comes from
`git ls-files "*.lean"` in `ROOT`. `FULL_DEPENDENT_CHECK` at the top of `impmin.py`
switches off stage 1b's final compile of all dependents except the root file (faster; a
dependent that breaks is then only noticed when it is processed itself, which stops the
run instead of rejecting the removal).

## Assumptions and known limits

- **Module system only.** Every project file must be a `module` file. Non-module files
  are parsed but the public/private logic was never exercised on them.
- **"Needed" means "the compiler fails without it".** If `simp` still closes a goal
  without a lemma it used before, that lemma's module does not count as needed.
- **Order dependence.** The result is minimal for the processing order used; another
  order can give a different, equally valid result.
- **`meta` imports are not optimised.** They are kept verbatim in every stage. A module
  that a file needs only through a kept `meta import` cannot be added by stages 2 and 3;
  such a file stops the run with "nothing left to add".
- **Imports that exist only for an `open`.** `open Filter` needs the namespace to exist,
  so a file can end up importing e.g. `Mathlib.Order.Filter.Defs` without using anything
  from it. The scripts never edit non-import lines; such imports show up in the result
  with an "unknown namespace" error and no witness declaration.
- **Non-weak `-D` options.** If the lakefile sets an option without `weak.` (Sphere-Packing:
  `linter.flexible = false`), every file must load the module defining it, which can
  force an otherwise unused import (`Mathlib.Init` in `Tactic/TendstoContAttr.lean`).
- **Cross-file effects.** During a run each file is compiled against the final state of
  what it imports, and stage 1b compiles all dependents of a changed file, including the
  root file. A dependent is still compiled against the old oleans of the files between it
  and the changed file; anything depending on that is caught by the final check of the run
  (or by the final `lake build`), not traced back to a single change.
- **Transient failures.** A compile killed by a timeout or the OOM killer is retried once
  and then stops the run; it is never taken as evidence. If memory is tight, lower
  `IMPMIN_WORKERS`.
- **The scratch location matters.** The first runs kept everything under `/tmp`, and a
  reboot wiped it mid-run. Keep this folder somewhere durable.
- **Do not run `lake build` during a run.** The shadow tree is a hardlink copy of the
  build directory taken at the start. Between `run` and `apply` it is fine.

## Ideas for further work

- Read `ROOT_MODULE` and `OPTS` from the lakefile instead of hardcoding them (today
  `OPTS` is only checked against Lake's `.setup.json`).
- Handle `meta` and `public meta` imports in stages 2 and 3.
- Optionally report or remove unused `open` namespaces instead of importing for them.

## Records of the Sphere-Packing runs (`runs-sphere-packing/`)

These were made by the earlier version of the scripts (separate `stage1.py`,
`refine.py`, `privatize.py`, `apply_*.py`), so the file names differ from today's
`work/` layout. Stage 1b was then called "stage2" and edited the sources directly.

| File | Content |
|---|---|
| `base_times.json` | Per-file compile time and peak memory (today: `baseline`). |
| `stage2.out`, `stage2.jsonl`, `stage2_state.json` | Stage 1b: progress output, every trial, and the removed imports per file. |
| `needs.tsv`, `refine.out`, `refine.jsonl`, `refine_result.json` | Stage 2: first-guess data, progress, every compile, and per file the old and new imports with a witness declaration (`why`). |
| `needs2.tsv`, `privatize.out`, `privatize.jsonl`, `privatize_result.json` | Stage 3, same layout; `pub` and `priv` lists per file. |

Timings on a 14-core laptop with 15 GB RAM, 4 workers: stage 1b 587 s (349 compiles),
stage 2 about 17 min (426 compiles), stage 3 about 29 min (829 compiles); a full
`lake build` of the project takes about 90 s.

The merged `impmin.py`, run end to end on the same machine from the same commit (November
2026), gives the same import counts at every stage (265 → 162 → 133 → 157 → 243; 114
public, 128 private, 1 public meta), with stage 1b in about 17 min (564 compiles), stage
2 in about 6 min (380 compiles) and stage 3 in about 11 min (578 compiles); every `lake
build` and `mk_all --check` passed. (Its working files were kept locally in `work/`, which
is not committed.)

The version after the review of 24 November 2026 (root file compiled as a dependent and
as a final check, `stdbuf`, critical-path scheduling, permission bits kept) was run again
on a clone at the same commit for stages 1a, 1b and 2. Each gave exactly the same import
lines in every file as before, each final check and `lake build` passed, and no file lost
its executable bit. Stage 1b took 561 s (624 compiles, 1669 s compile time; before:
1027 s, 2726 s); stage 2 took 251 s (381 compiles, 990 s compile time; before: 371 s,
1309 s). Stage 3 was not re-run.

Git branches on the fork `felixpernegger/Sphere-Packing-Lean`:
`minimize-imports` (stage 1 and the formatting) and `direct-private-imports`
(stages 2 and 3 in one commit on top).
