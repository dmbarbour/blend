# Blend's command line mirrors Bend's

`blend-command-mirrors-bend` · maintainer · rev de48ae7

**Context.** Blend runs through scripts: `run.sh` builds the tool once
for each version of its sources and of Bend, and runs it with a stage's
name or `emit`; under `bend blend.bend` a dashed argument is Bend's.
The maintainer (2026-11-04, 2026-11-05) asked for a `blend` command of
its own, and (2026-11-06) for it to reflect Bend's, a `--tree` to emit
what a module reaches and a `deps` to list it, a dry run.

**Decision.** The maintainer (2026-11-06):
- `blend` takes a file first, as `bend` does, flags choosing what it
  does with it: `blend FILE.blend [args]`, `-o OUT`, `--check-only` and
  `--verdict` emit the module and hand its `FILE.bend` to Bend with the
  same arguments. Words name the rest: `emit [--alone|--tree]`,
  `deps [--make]`, `show` (the stages, and a name's resolution, as
  `bend base NAME`), `guide` and `version`. A first argument ending in
  `.blend` is a file, any other a word.
- Blend's errors take Bend's shape, `Error:` and `Location:` with the
  lines around it; Bend's errors on emitted code are mapped back to the
  `.blend` line they come from (`where.sh`'s rule, `README.md`).
- `deps` lists the modules `emit --tree` would reach, in the order it
  writes them, each current, stale, missing, refused or a package's,
  and exits 1 where any is not current, as `make -q` does; `--make`
  prints them as a makefile's rules. It learns staleness as import
  verification does, by emitting in memory, until a stamp in each
  emitted header makes it a line read.
- `blend` lives beside `bend`, in `$BEND_HOME/bin` (`~/.bend/bin`) by
  default; Bend's installer replaces only its own files there.

**Consequences.**
- `run.sh` and `bend blend.bend -- ...` give way to the command; the
  build stays cached, rebuilt when Bend or Blend changes.
- Each form has samples of its output and status, as `emit` has.
- `check_generated.sh` may become a `deps` per directory.
- Whether `blend FILE.blend` and its flags emit the module's tree or
  only verify its imports is the plan's to settle (`blend-cli.bend`).

**Rule lives in:** `docs/plans/Blend_2026-11-04.md`, `blend-cli`, until
the command is built; then `README.md`, Status.
