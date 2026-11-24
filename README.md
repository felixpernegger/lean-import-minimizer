# Lean import minimiser

This project provides an alternative to `lake shake` which does not relied on`.olean`'s and thus is much stabler. Instead, it largely follows a more brute-force approach (transversing the import graph in an efficient manner to avoid rebuilds as much as possible).

For more details, see the AI generated description following this senteence.

Minimises the imports of a Lean 4 project that uses the module system (`module`,
`public import`, `import`), without `lake shake`. The compiler decides every change: an
import is removed, replaced or made private only after a compile shows that the file (and,
where relevant, its dependents) still works.

It has been used on
[Sphere-Packing-Lean](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean)
(Lean v4.36.0, 72 files) only. The project path, root module and `-D` options are
hardcoded; set them before using it elsewhere (see [Settings](#settings)).

## Usage

`impmin.py run STAGE` decides the new import lists and writes `work/STAGE/result.json`; it
never edits the sources. `impmin.py apply STAGE` shows the change, `--apply` writes it,
`--apply --build` also runs `lake build`. Start from a clean git state, so each stage can be
reviewed with `git diff` and undone with `git checkout`.

```bash
python3 $T/impmin.py run implied              # 1a: instant, graph only
python3 $T/impmin.py apply implied --apply --build
python3 $T/impmin.py run remove               # 1b
python3 $T/impmin.py apply remove --apply --build
python3 $T/impmin.py verify-diff --table      # HEAD minus import lines only?
python3 $T/impmin.py format --apply           # Mathlib-style blocks, same imports
python3 $T/impmin.py run direct               # 2
python3 $T/impmin.py apply direct --apply --build
python3 $T/impmin.py run private              # 3
python3 $T/impmin.py apply private --apply --build
lake exe mk_all --check --module
rm -rf .lake/import-min
```

(`T` is this folder.) Build after every `apply`: a fresh `run` refuses to start unless
`lake build --no-build` succeeds, and `lake build` is the only check in the real build
order. Do not run `lake build` while a run is unfinished; `--build` refuses to.

On Sphere-Packing with 4 workers, stage 1b takes about 10 min, stage 2 about 4 min and
stage 3 about 10 min.

| `run` option | Effect |
|---|---|
| `--limit N` | Process at most N more files, then stop. |
| `--fresh` | Discard an unfinished run of this stage and start over. |
| `--no-guess` | `direct`/`private`: ignore the first guess (slow; for measuring it). |

**Resuming.** `run STAGE` continues an unfinished run if its shadow tree still exists
(otherwise use `--fresh`). Ctrl-C records nothing half-done. Before every file the sources
are checked against the state the run started from: unfinished files must have their
original imports, finished files their original or new ones, and nothing outside import
lines may have changed. So you can `apply` a partial result and resume afterwards (the
tree may not build until the run is finished and applied).

Other commands: `baseline` (compile every file once, for timeouts), `shadow` (recreate the
shadow tree), `selftest` (check that an olean installed in the shadow is the one dependents
load). `IMPMIN_WORKERS` sets how many `lean` processes run at once (default 4, safe with
about 6 GB free RAM). Keep this folder somewhere durable, not under `/tmp`: runs can take a
while and resume from `work/`.

## Stages

| Stage | `STAGE` | Rule | Sphere-Packing |
|---|---|---|---|
| 1a | `implied` | Delete imports implied by another import of the same file (graph only). | 265 → 162 |
| 1b | `remove` | Delete every import that the file and all its dependents compile without. | 162 → 133 |
| 2 | `direct` | Every import must itself provide something the file uses; pass-through imports are replaced by the modules actually used. | 133 → 157 |
| 3 | `private` | Every import gets the weakest modifier that compiles. | 157 → 243 (114 public, 128 private, 1 public meta) |

Stages 1a/1b delete lines in place; stages 2/3 rewrite the import block in Mathlib order.
The count goes up in 2 and 3 on purpose: a file that got a module through a re-export now
names it. `meta` imports, `import all` imports and the root file are never changed (the root
must keep listing every module for `mk_all`).

### Exact definitions

**1a, `implied`.** In file `C`, `import A` is dropped if another import `C → Y` reaches `A`
through `public`, non-`meta` imports and `Y`'s import is at least as visible as `A`'s. The
stage checks that every file sees and re-exports exactly the same modules afterwards.

**1b, `remove`.** An import is removed if the file and every dependent still compile without
it; nothing is ever added. Once a file's removals are decided, its dependents are compiled
against its new olean, and if one fails all removals of that file are rejected. The root
file is always among these dependents: it alone loads every file at once, so it catches
clashes no single file sees (e.g. an auto-named instance `instFoo_1` that becomes `instFoo`
and collides with another module's).

**2, `direct`.** For file `D` with import list `C`: `D` compiles with exactly `C`; for every
`M` in `C`, replacing `M` by `M`'s own public imports breaks `D`; imports implied through
public chains stay omitted. Private, `meta` and `import all` imports are kept as they are.

**3, `private`.** For file `D` with lists `pub` and `priv`: `D` compiles with them; for
every `M` in `pub`, "`M` private, everything below it public" breaks `D`; for every `M` in
`priv`, "`M` replaced by everything below it, private" breaks `D`. A file that needs `M`
only in proofs but something below `M` in statements gets `import M` plus a `public import`
of the lower module. `meta` and `import all` imports are kept as they are.

### How stages 2 and 3 find the imports

They start from a **first guess**: `needs.lean` loads the built project and lists, per
file, the modules whose declarations it uses and the module uses Lean records while
elaborating (notation, tactics, attributes), each marked as used publicly or only in
proofs. The guess compiles for most files (63 of 72 on Sphere-Packing).

When a list does not compile, the missing module is **searched** by compiling: a parallel
bisection over everything the file could see originally, in dependency order. It assumes
that adding imports never breaks a file. Cheaper candidates are tried first, each confirmed
by a compile: for `unknown namespace N`, a module that declares `N`; then the modules named
in the error plus the current imports; then modules that put attributes on used
declarations.

Then every import is **certified**: its test from the definitions above must fail. Tests
run in parallel; imports whose test passes are removed (or demoted) and the remaining
tests run again on the new lists.

## How it works

Lake rebuilds every dependent of a changed file, even when the change is reverted, which
would make each trial take minutes. So Lake is only used before a run and after `apply`.
In between:

- **Direct `lean` calls** in the `lake env` environment, killed at the first error. Only a
  Lean error means "does not compile". A timeout, crash or OOM kill is retried once with
  twice the time (timeout: 3 × baseline + 90 s), then stops the run; it is never taken as
  evidence.
- **Temporary sources**: a trial compiles a copy of the file with a new import block,
  produced exactly as `apply` would write it.
- **Shadow olean tree**: `.lake/import-min/lean` is a hardlink copy of
  `.lake/build/lib/lean` that the trials use instead. Each finished file's new olean is
  installed there, so later files compile against it, while Lake's build stays untouched.
- **Dependencies first**: files are processed in topological order, so everything a file
  loads is already final. Stages 2/3 run independent files in parallel; stage 1b is
  sequential.
- **Final check**: when a stage is done, the root file is compiled against the final shadow.
  If it fails, the run exits non-zero and `apply` refuses the result.
- **Lock**: only one command at a time may use the shadow or edit sources.

## Safety of `apply`

Every file is checked before anything is written: its import lines must be the result's
old lines (or already the new ones), its other lines unchanged since the run started, and
the result must be for this project and pass its final check. If any check fails, nothing
is written. Files keep their permission bits; running `apply` twice does nothing the second
time.

Supported headers: each import alone on its line (a trailing comment is fine); for
`direct`, `private` and `format`, no comment lines inside the import block. A fresh `run`
lists violating files and stops.

## Settings

In the settings block of `impgraph.py`:

| Setting | What |
|---|---|
| `ROOT` | Project path; overridden by `IMPMIN_ROOT`. |
| `ROOT_MODULE` | Root aggregator file, never touched. Only tracked files in its namespace are processed, and it must import each of them (transitively). |
| `OPTS` | The `-D` options Lake passes (mirror `leanOptions` from the lakefile); a fresh run checks them against Lake's build. |

The toolchain is found from `ROOT/lean-toolchain` in `~/.elan/toolchains`, the file list
from `git ls-files`. Setting `FULL_DEPENDENT_CHECK = False` in `impmin.py` makes stage 1b
check only the root file after each file's removals (faster; a broken dependent then stops
the run later instead of rejecting the removal).

## Known limits

- **Module system only**: non-module files are parsed but the public/private logic is
  untested on them.
- **"Needed" means "the compiler fails without it"**: if `simp` still closes a goal
  without a lemma, that lemma's module is not needed.
- **Order dependence**: the result is minimal for the processing order; another order can
  give a different valid result.
- **`meta` imports are not optimised**: a module needed only through a kept `meta import`
  cannot be added by stages 2/3 ("nothing left to add").
- **Imports only for an `open`**: `open Filter` needs the namespace to exist, so a file can
  import e.g. `Mathlib.Order.Filter.Defs` without using it.
- **Non-weak `-D` options** (e.g. `linter.flexible = false`) force every file to load the
  module that defines the option.
- **Cross-file effects**: a dependent is checked against older oleans of the files between
  it and the changed file; problems from that are caught by the final check or
  `lake build`, but not traced to one change.

## Files

| Path | Content |
|---|---|
| `impmin.py` | Entry point: all stages and commands. |
| `impgraph.py` | Settings, import-header parsing, the import graph, rewriting import blocks. |
| `needs.lean` | First-guess extraction. |
| `work/STAGE/` | Per stage: `result.json` (old and new imports per file), `log.jsonl` (every compile), `progress.out`, `run.json` (start state), `needs.tsv`, `final.json`. |
| `work/base_times.json` | Baseline compile times. |
| `runs-sphere-packing/` | Logs and results of example runs on Sphere-Packing. |
