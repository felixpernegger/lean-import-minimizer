# Lean import minimiser

This project provides an alternative to `lake shake` which does not rely on `.olean` files
and is thus much more stable. Instead, it follows a more brute-force approach (traversing
the import graph efficiently to avoid rebuilds as much as possible).

For more details, see the AI-generated description following this sentence.

---

## What it does

The scripts rewrite the import lines of a Lean 4 project that uses the module system
(`module`, `public import`, `import`). They work in four stages, and every change is kept
only if the compiler accepts it.

| Stage | Name | What it changes | Sphere-Packing (72 files) |
|---|---|---|---|
| 1a | `implied` | Drops imports that another import of the same file already provides. | 265 → 162 lines |
| 1b | `remove` | Drops imports that the file and all files depending on it compile without. | 162 → 133 |
| 2 | `direct` | Replaces imports that only pass other modules through by the modules actually used. | 133 → 157 |
| 3 | `private` | Turns `public import` into `import` wherever the file still compiles. | 157 → 243 |

The count goes up in stages 2 and 3 on purpose: each file then names the modules it uses
instead of getting them through someone else's re-export.

The scripts never change non-import lines, `meta import` lines, `import all` lines or the
root file of the project.

## Requirements

- Linux, Python 3.9 or newer, `elan`, and `stdbuf` (part of coreutils).
- A Lean 4 project that uses the module system, is a git repository and builds with
  `lake build`.

So far the scripts have only been used on
[Sphere-Packing-Lean](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean)
(Lean v4.36.0).

## Setup

Edit the settings at the top of `impgraph.py`:

| Setting | Meaning |
|---|---|
| `ROOT` | Path of the project. Can also be set with the environment variable `IMPMIN_ROOT`. |
| `ROOT_MODULE` | The root file that imports all others (e.g. `SpherePacking`). Only files in its namespace are processed. |
| `OPTS` | The `-D` options from `leanOptions` in the lakefile. A run checks them against Lake's build and stops if they differ. |

## Usage

Every stage works the same way:

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
rm -rf <project>/.lake/import-min             # clean up when done
```

Good to know:

- **Start from a clean git state.** Then every stage can be reviewed with `git diff` and
  undone with `git checkout`.
- **Build after every `apply`.** The next `run` needs an up-to-date build.
- **Do not run `lake build` while a run is unfinished.** The run uses a copy of the build
  that `lake build` would get out of sync with.
- **Runs can be interrupted.** Ctrl-C is safe, and running the same command again
  continues where it stopped. `--fresh` starts over instead.
- **Runtime:** on Sphere-Packing with 4 workers, stages 1b and 3 take about 10 minutes each
  and stage 2 about 4 minutes.

Options of `run`:

| Option | Effect |
|---|---|
| `--limit N` | Process at most N more files, then stop. |
| `--fresh` | Throw away an unfinished run of this stage and start over. |
| `--no-guess` | Stages 2 and 3: do not use the first guess (much slower). |

Other commands:

| Command | Effect |
|---|---|
| `format [--apply]` | Sort and space import blocks the Mathlib way, without changing which modules are imported. |
| `verify-diff [--table]` | Check that the project differs from `HEAD` only by deleted import lines (useful after stage 1, before `format`). |
| `baseline` | Compile every file once (used for timeouts; runs automatically when needed). |
| `selftest` | Check that the build copy works as intended. |

The environment variable `IMPMIN_WORKERS` sets how many `lean` processes run at once
(default 4; that needs about 6 GB of free memory).

## How it works

Changing one import with `lake build` rebuilds every file that depends on it, so a single
trial can take minutes. The scripts avoid that:

1. **They call `lean` directly** on a temporary copy of the file with the new imports. A
   change counts as failing only if Lean reports an error. Timeouts and crashes are
   retried once and never count as evidence.
2. **They compile against a private copy of the build** (`.lake/import-min`, made of
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
- **"Needed" means "the compiler fails without it".** If `simp` can still close a goal
  without some lemma, that lemma's module is not considered needed.
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
them in statements or only in proofs. The guess compiles for most files (63 of 72 on
Sphere-Packing). When a guess does not compile, the missing module is found by bisection:
the scripts compile the file with growing prefixes of all modules it could see before, in
dependency order. Every import in the result is then tested against the rules above, and
imports that pass their test are removed or made private.

## Files

| Path | Content |
|---|---|
| `impmin.py` | The command-line tool: all stages and commands. |
| `impgraph.py` | Settings, reading import headers, the import graph, rewriting import blocks. |
| `needs.lean` | Computes the first guess for stages 2 and 3. |
| `work/` | Created by runs: results, logs and progress of each stage. |
| `runs-sphere-packing/` | Logs and results of example runs on Sphere-Packing. |

## License

Apache License 2.0, see [LICENSE](LICENSE).
