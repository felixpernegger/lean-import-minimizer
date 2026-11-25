# Lean import minimiser

This project provides an alternative to `lake shake` which does not rely on `.olean` files
and is thus much more stable. Instead, it follows a more brute-force approach (traversing
the import graph efficiently to avoid rebuilds as much as possible).

For more details, see the AI-generated description following this sentence.

---

## What it does

The scripts rewrite the import lines of a Lean 4 project that uses the module system
(`module`, `public import`, `import`). They work in four stages, and every change is kept
only if the compiler accepts it, without new errors and without new warnings.

| Stage | Name | What it changes |
|---|---|---|
| 1a | `implied` | Drops imports that another import of the same file already provides. |
| 1b | `remove` | Drops imports that the file and all files depending on it compile without. |
| 2 | `direct` | Replaces imports that only pass other modules through by the modules actually used. |
| 3 | `private` | Turns `public import` into `import` wherever the file still compiles. |

Stages 1a and 1b lower the number of import lines. Stages 2 and 3 raise it again on
purpose: each file then names the modules it uses instead of getting them through someone
else's re-export. See [Example run](#example-run) for numbers.

The scripts never change non-import lines, `meta import` lines, `import all` lines or the
root file of the project, and they respect `lake shake`'s `shake:` annotations
(see [What is kept](#what-is-kept)).

## Requirements

- Linux, Python 3.9 or newer, `elan`, and `stdbuf` (part of coreutils).
- A Lean 4 project that uses the module system, is a git repository and builds with
  `lake build`.

The scripts have been used on
[Sphere-Packing-Lean](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean)
(Lean v4.36) and [CSLib](https://github.com/leanprover/cslib) (Lean v4.37).

## Setup

Nothing to edit. Run the scripts from the project's directory, or name it:

| Option (before the command) | Environment variable | Meaning |
|---|---|---|
| `--project PATH` | `IMPMIN_ROOT` | The project. Default: the current directory. |
| `--root-module NAME` | `IMPMIN_MODULE` | The root file that imports all others (e.g. `Mathlib`). Only files in its namespace are processed. Default: the top-level `X.lean` that has a directory `X/`; if there are several, the one the lakefile names as default target. |

The options Lean is called with (`leanOptions` in the lakefile) are read per file from
the `.setup.json` files that `lake build` writes.

`IMPMIN_WORKERS` sets how many `lean` processes run at once (default 4; that needs about
6 GB of free memory on a Mathlib-based project).

## Usage

Every stage works the same way (`impmin.py` stands for the path of this repository's
`impmin.py`, run from the project's directory):

```bash
python3 impmin.py run STAGE                   # decide the new imports (sources untouched)
python3 impmin.py apply STAGE                 # show what would change
python3 impmin.py apply STAGE --apply --build # write the changes, then run lake build
```

The full sequence:

```bash
python3 impmin.py run implied && python3 impmin.py apply implied --apply --build
python3 impmin.py run remove  && python3 impmin.py apply remove  --apply --build
python3 impmin.py format --apply              # optional: sort import blocks Mathlib-style
python3 impmin.py run direct  && python3 impmin.py apply direct  --apply --build
python3 impmin.py run private && python3 impmin.py apply private --apply --build
rm -rf .lake/import-min                       # clean up when done
```

Good to know:

- **Start from a clean git state.** Then every stage can be reviewed with `git diff` and
  undone with `git checkout`.
- **Build after every `apply`.** The next `run` needs an up-to-date build.
- **Do not run `lake build` while a run is unfinished.** The run uses a copy of the build
  that `lake build` would get out of sync with.
- **Runs can be interrupted.** Ctrl-C is safe, and running the same command again
  continues where it stopped. `--fresh` starts over instead.
- **Check what the build does not cover.** `apply ... --build --check 'lake test'` runs
  the given command after `lake build`, e.g. the project's tests, linters or other
  libraries (see [Limitations](#limitations)).

Options of `run`:

| Option | Effect |
|---|---|
| `--limit N` | Process at most N more files, then stop. |
| `--fresh` | Throw away an unfinished run of this stage and start over. |
| `--redo MODULE...` | Forget the results of these files and of every file depending on them, then continue the run. Their import lines may have been changed in comments only (e.g. an added `-- shake: keep`), and the comment on their `module` line may have changed. |
| `--allow-new-warnings` | Only errors count as failure (taken at the start of a run). |
| `--no-guess` | Stages 2 and 3: do not use the first guess (much slower). |

Other commands:

| Command | Effect |
|---|---|
| `format [--apply]` | Sort and space import blocks the Mathlib way, without changing which modules are imported. |
| `verify-diff [--table]` | Check that the project differs from `HEAD` only by deleted import lines (useful after stage 1, before `format`). |
| `baseline` | Compile every file once, recording its time and warnings (runs automatically when needed). |
| `selftest` | Check that the build copy works as intended. |

Everything a run writes (results, logs, the build copy) is in the project's
`.lake/import-min`.

## What is kept

Some imports are needed for reasons a compile of the file itself does not show. These are
kept:

- **`lake shake`'s annotations** (only the comments are read; `lake shake` is never run):
  - `import X -- shake: keep`: this line is never changed.
  - `module -- shake: keep-all`: no import of this file is removed or changed. Stages 2
    and 3 may still add imports if the file stops compiling otherwise.
  - `module -- shake: keep-downstream` in file `K`: every file that re-exports `K` keeps
    re-exporting it, and every file that sees `K` keeps seeing it, adding
    `public import K` or `import K` where needed. Use this for a file like `Mathlib.Init`
    that every file must reach.
- **Files with nothing but imports** (and comments) are treated like `keep-all`: they only
  pass modules on, so the compiler cannot tell which of them are needed.
- **Imports that macros and notation depend on.** A syntax quotation (in `macro`,
  `notation`, `elab`, ...) resolves the names it contains in the file where it is written.
  If that file stops seeing such a name, the file itself still compiles, but every file
  using the macro fails with ``Unknown identifier `X✝` ``. So each file keeps seeing,
  at the level it had (public or private), every module whose constants its quotations
  name. `needs.lean` finds these names in the compiled code. If a file still fails with a
  `✝` error, mark the import in the macro's file `-- shake: keep` and rerun with
  `--redo` that file.

A run lists the lines it keeps for these reasons (`kept (pinned)` in stage 1b, `pinned` in
the summaries of stages 2 and 3).

## Warnings

The first run compiles every file once as it is and records its warnings. Afterwards a
trial counts as failing if it produces a warning the file did not have (compared by text,
ignoring positions), e.g. "This simp argument is unused" when an import changes what
`simp` finds. This also holds for the files depending on a changed file in stage 1b.
`--allow-new-warnings` turns this off for a run.

If a stage finds no import set without a new warning, it keeps the file's imports as they
were at the start of the stage. If even those do not work (the warning comes from a change
in a file it imports), the run stops and names the file.

## How it works

Changing one import with `lake build` rebuilds every file that depends on it, so a single
trial can take minutes. The scripts avoid that:

1. **They call `lean` directly** on a temporary copy of the file with the new imports. A
   change counts as failing only if Lean reports an error or a new warning. Timeouts and
   crashes are retried once and never count as evidence.
2. **They compile against a private copy of the build** (`.lake/import-min/lean`, made of
   hardlinks, so it costs no disk space). When a file is done, its new `.olean` goes into
   this copy, and Lake's own build stays untouched.
3. **They process files in dependency order**, so everything a file imports is already
   final. In stages 2 and 3, independent files are processed in parallel.
4. **At the end of stages 1b, 2 and 3 they compile the root file**, which loads all files
   together. If that fails, `apply` refuses the result.

`apply` checks every file before writing anything: its imports and the rest of the file
must be exactly as they were when the run started. If any file has changed, nothing is
written.

## Limitations

- **Module system only.** Files without `module` are read but were never tested.
- **"Needed" means "the compiler fails without it, or warns".** If `simp` can still close
  a goal without some lemma, and no linter notices, that lemma's module is not considered
  needed.
- **Import order can change elaboration.** Lean loads imports in the order they are
  written, and the order decides ties, e.g. which instance or `gcongr` lemma is found
  first. Stages 2 and 3 and `format` sort import blocks, so a file can elaborate
  differently with the same modules. Errors and new warnings in the file itself are caught;
  a changed result that only shows in a file depending on it is caught in stage 1b but not
  in stages 2 and 3. If this happens, mark the file `module -- shake: keep-all` (then its
  block is not rewritten) and rerun with `--redo` that file.
- **Only the root module's files are checked.** Files of other libraries in the same
  project (tests, scripts) that import it are neither processed nor compiled during a run,
  so making an import private can break them. Use `apply ... --build --check CMD` with a
  command that builds them, and run the project's own linters there too (an environment
  linter that only `lake lint` runs is not seen by a compile).
- **The result depends on the processing order.** Another order can give a different, also
  valid result.
- **`meta` imports are kept as they are.** If a file needs a module only through a
  `meta import`, stages 2 and 3 stop with "nothing left to add".
- **`open` can force imports.** `open Filter` needs a module that declares `Filter`, even
  if nothing else from it is used.
- **Options set without `weak.`** in the lakefile force every file to import the module
  that defines the option.
- **Header layout.** Each import must be on its own line (a trailing comment is fine). For
  stages 2 and 3 and `format`, the import block must not contain comment lines. A run
  lists files that break this and stops.

## Reference: the exact rules

Lines kept by the rules in [What is kept](#what-is-kept) are left out of all tests below,
and the pinned modules are treated as imported.

**Stage 1a (`implied`).** In file `C`, `import A` is dropped if another import of `C`
reaches `A` through a chain of public, non-`meta` imports and is at least as visible as
`import A`. Every file must see and re-export exactly the same modules afterwards.

**Stage 1b (`remove`).** An import is dropped if the file and every file depending on it
still compile without it. Nothing is ever added. After a file's removals are decided, the
files depending on it, including the root file, are compiled again against its new
`.olean`; if one fails, all removals of that file are undone. The root file catches
clashes that no single file sees, such as an auto-named instance `instFoo_1` turning into
`instFoo` and colliding with another module's `instFoo`.

**Stage 2 (`direct`).** For a file `D` with imports `C`:

- `D` compiles with exactly `C`;
- for every `M` in `C`, replacing `M` by the public imports of `M` breaks `D`;
- an import already provided by another import of `D` is left out.

Private, `meta` and `import all` imports are kept as they are.

**Stage 3 (`private`).** For a file `D` with public imports `pub` and private imports
`priv`:

- `D` compiles with them;
- for every `M` in `pub`, making `M` private (with everything below it public) breaks `D`;
- for every `M` in `priv`, replacing `M` by everything below it (private) breaks `D`.

A file that needs `M` only in proofs but something below `M` in its statements ends up with
`import M` plus a `public import` of the lower module. `meta` and `import all` imports are
kept as they are.

**How stages 2 and 3 find imports.** They start from a first guess made by `needs.lean`,
which reads the built project and lists the modules each file uses, and whether it uses
them in statements or only in proofs. The guess compiles for most files. When a guess does
not compile, the missing module is found by bisection: the scripts compile the file with
growing prefixes of all modules it could see before, in dependency order. Every import in
the result is then tested against the rules above, and imports that pass their test are
removed or made private.

## Files

| Path | Content |
|---|---|
| `impmin.py` | The command-line tool: all stages and commands. |
| `impgraph.py` | Project settings, reading import headers, the import graph, rewriting import blocks. |
| `needs.lean` | Reads the built project: the first guess for stages 2 and 3, and the names in syntax quotations. |
| `runs-sphere-packing/` | Logs and results of example runs on Sphere-Packing. |
| `<project>/.lake/import-min/work/` | Created by runs: results, logs and progress of each stage. |

## Example run

Sphere-Packing-Lean, 72 files, 4 workers:

| Stage | Import lines | Time |
|---|---|---|
| 1a `implied` | 265 → 162 | seconds |
| 1b `remove` | 162 → 133 | about 10 minutes |
| 2 `direct` | 133 → 157 | about 4 minutes |
| 3 `private` | 157 → 243 | about 10 minutes |

The first guess of stages 2 and 3 compiled for 63 of the 72 files.

## License

Apache License 2.0, see [LICENSE](LICENSE).
