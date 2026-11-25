# CLAUDE.md

## What this project is

An alternative to `lake shake`: scripts that minimise the imports of a Lean 4 project
using the module system (`module`, `public import`, `import`). Unlike `lake shake`, every
change is decided by the compiler: an import is removed, replaced or made private only
after a compile of the affected file (and its dependents, where relevant) shows it still
works.

`README.md` is the full documentation: the three stages, their exact definitions, how
rebuilds are avoided (direct `lean` calls, shadow olean tree), how to run it, what is
kept and why, and the known limits. Read it before changing the pipeline, and keep
it up to date when behaviour changes. It is written for users of the scripts: keep it
concise, and leave out history (earlier versions, past runs, reviews, timings of old
versions) and internal code names that a user does not need.

## Do not use `lake shake`

This project must not use `lake shake`, in any form:

- Never call `lake shake` (or `lake exe shake`) from the scripts, and do not run it on a
  target project as a shortcut, a cross-check or a fallback.
- Reusing code from Lake's shake source in `needs.lean` is fine. What matters is that
  nothing derived from oleans decides a change: `needs.lean` reads the same raw data
  `lake shake` reads (constants in compiled terms plus `Lean/ExtraModUses.lean`), and its
  output is only a first guess that the compile-based search corrects. Never treat it as
  the final answer without a compile. Reading `shake:` annotation comments is fine too.

## Working rules

- The compiler is the only judge. A change counts as valid only if a compile shows it,
  with no new errors and no warnings beyond the file's baseline. Olean-derived data
  (`needs.lean`) may only make the scripts keep more (pins for syntax quotations), never
  accept a change.
- Avoid `lake build` during runs: it rebuilds every dependent of a changed file. Use
  `lake build` only for the baseline and the final verification, and never while a run
  is using the shadow tree (`.lake/import-min/lean`).
- Never edit non-import lines of a target project's sources.
- `meta` imports, the root aggregator file and lines kept by `shake:` annotations are left
  untouched (see README, "What is kept").
- Nothing may be specific to one target project. The project, the root module and the
  `-D` options come from the command line, the environment and Lake's `.setup.json`
  files; run state lives in the target's `.lake/import-min`. Sphere-Packing appears only
  as an example run in the README and in `runs-sphere-packing/`.
- `impmin.py` is the single entry point. Stages 2 and 3 share one class (`Refine`);
  keep stage differences as settings there rather than splitting the code again.
- `run` never edits the target's sources; only `apply` does.
- Keep long-running state in durable locations, not `/tmp` (a reboot wiped an earlier
  run).
- `runs-sphere-packing/` holds records of past runs; do not overwrite it.
