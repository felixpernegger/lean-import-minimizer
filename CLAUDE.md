# CLAUDE.md

## What this project is

An alternative to `lake shake`: scripts that minimise the imports of a Lean 4 project
using the module system (`module`, `public import`, `import`). Unlike `lake shake`, every
change is decided by the compiler: an import is removed, replaced or made private only
after a compile of the affected file (and its dependents, where relevant) shows it still
works.

`README.md` is the full documentation: the three stages, their exact definitions, how
rebuilds are avoided (direct `lean` calls, shadow olean tree), how to run it, the
hardcoded settings and the known limits. Read it before changing the pipeline, and keep
it up to date when behaviour changes.

## Do not use `lake shake`

This project must not use `lake shake`, in any form:

- Never call `lake shake` (or `lake exe shake`) from the scripts, and do not run it on a
  target project as a shortcut, a cross-check or a fallback.
- Reusing code from Lake's shake source in `needs.lean` is fine. What matters is that
  nothing derived from oleans decides a change: `needs.lean` reads the same raw data
  `lake shake` reads (constants in compiled terms plus `Lean/ExtraModUses.lean`), and its
  output is only a first guess that the compile-based search corrects. Never treat it as
  the final answer without a compile.

## Working rules

- The compiler is the only judge. A change counts as valid only if a compile shows it.
- Avoid `lake build` during runs: it rebuilds every dependent of a changed file. Use
  `lake build` only for the baseline and the final verification, and never while a run
  is using the shadow tree (`.lake/import-min/lean`).
- Never edit non-import lines of a target project's sources.
- `meta` imports and the root aggregator file are left untouched (see README).
- The project path, the root module and the `-D` options are hardcoded for
  Sphere-Packing-Lean (settings block at the top of `impgraph.py`); see "Hardcoded
  settings" in the README before running on anything else.
- `impmin.py` is the single entry point. Stages 2 and 3 share one class (`Refine`);
  keep stage differences as settings there rather than splitting the code again.
- `run` never edits the target's sources; only `apply` does.
- Keep long-running state in durable locations, not `/tmp` (a reboot wiped an earlier
  run).
- `runs-sphere-packing/` holds records of past runs; do not overwrite it.
