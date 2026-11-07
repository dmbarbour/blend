# A stamp in each written file says whether it is current

`blend-stamps` · maintainer · rev 766d76c

**Context.** Knowing whether a written `.bend` is current cost its
emission again, in memory, compared byte for byte: `deps` did so for
every module, and `emit` wrote a module's whole tree every time. The
plan asked for a stamp in each emitted header, a hash of its sources
and of Blend, read in its place (`blend-cli.stamps`).

**Decision.** The maintainer (2026-11-07): the stamp records Blend's
version stamp, blend.bend's hash, written into `blend_stamp.bend` by
`blend_stamp.sh`, which the pre-commit hook runs on blend.bend as staged.
Every change to blend.bend moves it, erring toward too many updates: a
format bumped by hand was missed when a fix changed what Blend writes
for inputs no sample showed (`blend-scale.copies-fuel`), and the files
the Blend before wrote stayed current. The script never overwrites a
change to the file it did not make: it refuses, the gate with it, so
that the change is reviewed. Named for a version stamp, not a format,
which reads as an auto-formatter's. A stamp resting on more than the
tool's source may come later. `blend version` reports the version
stamp.

The rest is the agent's:
- The stamp is a written file's second line, `# blend stamp: VERSION
  HASH`, after the header: the version stamp, and 64 bits of hash (two
  32-bit FNV-1a lanes, their multipliers differing) over the version
  stamp and the
  module's tree as read, each module's path from the module's own
  directory and its bytes. A plain Bend import is not read, and is no
  part of it.
- A file whose stamp is what its sources give now is current. `deps`
  reads the stamp, emitting in memory only where a file is not current,
  to tell stale from refused; `deps --bytes` emits each and compares the
  bytes too, finding a file stamped current but other.
- `emit` leaves a module current by its stamp as it is, a module named
  no different from an import, and `--force` writes every one all the
  same (the maintainer, 2026-11-07). It lists a current file after those
  written, and checks it with the rest of the tree, so that a failing
  law in it is still found and mapped. `deps --make`'s recipe forces
  the write, so that make finds the target's time moved; the gate's
  "regenerate it" too, a file edited under its stamp being current.
- The gate (`check_generated.sh`) checks `blend_stamp.bend` against
  blend.bend and runs `deps --bytes` over the samples, so that every
  change to blend.bend writes them again in the same commit. `blend
  --version-stamp` prints the tool's.

**Consequences.**
- Updating Blend leaves every file it wrote stale: each is written again
  once (`emit` writes it, `deps` lists it stale), a comment's change to
  blend.bend too.
- A commit changing blend.bend carries every sample written again, their
  stamps moved; a change in what they hold beyond the stamp shows in
  their diff.
- glam-in-bend's modules are written again with each new Blend its
  pointer records.
- Packages can be told stale by their stamps (`blend-packages`).

**Rule lives in:** `blend.bend`, Stamps (`blend.version`); `blend_stamp.sh`;
`GUIDE.md`, What Blend writes.
