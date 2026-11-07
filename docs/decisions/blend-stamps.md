# A stamp in each written file says whether it is current

`blend-stamps` · maintainer · rev 1633393

**Context.** Knowing whether a written `.bend` is current cost its
emission again, in memory, compared byte for byte: `deps` did so for
every module, and `emit` wrote a module's whole tree every time. The
plan asked for a stamp in each emitted header, a hash of its sources
and of Blend, read in its place (`blend-cli.stamps`).

**Decision.** The maintainer (2026-11-07): the stamp records of Blend a
format version, bumped when what Blend writes changes, not a hash of
Blend itself, which would restamp every file, and so regenerate and
recheck it, on every change to Blend. `blend version` reports the
format.

The rest is the agent's:
- The stamp is a written file's second line, `# blend stamp: FORMAT
  HASH`, after the header: the format, and 64 bits of hash (two 32-bit
  FNV-1a lanes, their multipliers differing) over the format and the
  module's tree as read, each module's path from the module's own
  directory and its bytes. A plain Bend import is not read, and is no
  part of it.
- A file whose stamp is what its sources give now is current. `deps`
  reads the stamp, emitting in memory only where a file is not current,
  to tell stale from refused; `deps --bytes` emits each and compares the
  bytes too, finding a file stamped current but other.
- `emit` writes the modules named; an import current by its stamp it
  leaves as it is, but lists after the files written, and checks with
  the rest of the tree, so that a failing law in a current import is
  still found and mapped.
- The gate (`check_generated.sh`) runs `deps --bytes` over the samples,
  and fails a generated file that changed while its stamp stayed as
  HEAD has it: Blend's output changed under one format. `blend
  --format` prints the tool's format.

**Consequences.**
- Updating Blend leaves a tree current unless the format moved.
- A change in what Blend writes that no sample shows could slip past
  the gate under an unchanged format: the samples are the specification.
- Packages can be told stale by their stamps (`blend-packages`).

**Rule lives in:** `blend.bend`, Stamps (`blend.format`);
`GUIDE.md`, What Blend writes.
