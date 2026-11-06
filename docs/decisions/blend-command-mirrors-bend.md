# Blend's command line mirrors Bend's

`blend-command-mirrors-bend` · maintainer · rev f49e386

**Context.** Blend runs through scripts: `run.sh` builds the tool once
for each version of its sources and of Bend, and runs it with a stage's
name or `emit`; under `bend blend.bend` a dashed argument is Bend's.
The maintainer (2026-11-04, 2026-11-05) asked for a `blend` command of
its own, and (2026-11-06) for it to reflect Bend's, a `--tree` to emit
what a module reaches and a `deps` to list it, a dry run.

**Decision.** The maintainer (2026-11-06):
- `blend` takes a file first, as `bend` does, flags choosing what it
  does with it: `blend FILE.blend [args]`, `-o OUT`, `--check-only` and
  `--verdict` emit the module's tree and hand its `FILE.bend` to Bend
  with the same arguments, the launcher running Bend so that the
  program keeps its input, output and status (Bend's `Process.run`
  captures output, bounded). Words name the rest: `emit [--alone]`,
  `deps [--make]`, `show` (the stages, and a name's resolution, as
  `bend base NAME`), `guide`, `version`, `update` and `rebuild`. A first
  argument ending in `.blend` is a file, any other a word; flags may
  follow anywhere, `--` passing the rest to the program, as Bend's.
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
- The launcher, a shell script, runs the tool built natively, cached and
  built again when Blend or Bend changes; where no native build can be
  made (no clang), it runs `bend blend.bend --`, slower. Should Bend
  check incrementally, running through Bend may become the default (the
  maintainer, 2026-11-06).
- Blend installs from a checkout, for its development, or from a
  release, by an installer that installs Bend first where it is
  missing; releases from Bend's hub, by name or hash, or the
  repository's. `BLEND_VERSION` pins one; no `@latest` is followed,
  against a release slipped in: the launcher reports a later release,
  never takes it. `blend update` installs a later release, `blend
  rebuild` builds the tool again.
- Unless `BEND_NO_TELEMETRY` is set, the launcher reports a later
  release (asking at most daily) and, apart, a Bend changed since the
  tool was built, the chance to rebuild.
- To weigh: a package's file run by name, and a script given inline, as
  asked of Bend (#2083).

**Consequences.**
- `run.sh` and `bend blend.bend -- ...` give way to the command; the
  build stays cached, rebuilt when Bend or Blend changes.
- Each form has samples of its output and status, as `emit` has.
- `check_generated.sh` may become a `deps` per directory.
- `blend FILE.blend` and its flags emit the module's tree, as `emit`
  does (the maintainer, 2026-11-06), beside its sources
  (`blend-cli.out`).

**Rule lives in:** `docs/plans/Blend_2026-11-04.md`, `blend-cli`, until
the command is built; then `README.md`, Status.
