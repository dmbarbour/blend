# Emission writes a module's tree, or the modules named alone

`blend-emit-verifies-imports` · maintainer · rev f49e386

**Context.** A module's emission depends on nothing that imports it:
every definition is emitted and no top-level object can be extended, so
`emit` takes several modules at once (`README.md`). Writing files a
command did not name could not last once packages came: a package's
emitted files are its own (`blend-packages`); and left alone, an import
emitted by no command goes stale unseen. So `emit` first wrote the
modules it named and verified their imports, emitting each again in
memory and comparing it with the files beside it (the maintainer,
2026-11-05). Imports are now local, never `../` or `/`
(`blend-imports-local`): every module a tree reaches lies in the user's
own directories.

**Decision.** The maintainer (2026-11-06): `emit` writes the modules it
names and every import they reach, its tree, imports first, all or none
as ever; it stops at a package's boundary, a package's modules verified,
never written. `emit --alone` writes the modules named, and no other.
The mode that wrote the modules named and verified the rest goes:
`deps` reports what is stale without writing anything
(`blend-command-mirrors-bend`).

**Consequences.**
- A package's verification, and `deps`, cost each module's emission
  again; since `blend-stamps`, a stamp in each written file's header
  makes it a line read.
- `bend blend.bend -- emit --alone ...` under Bend, whose CLI takes a
  dashed argument as its own; the built tool takes it directly.
- `blend deps` lists what `emit` would reach and whether each is
  current, a dry run of it (`blend-command-mirrors-bend`).
- check_generated.sh emits each directory's modules `--alone`, each
  directory checked on its own; samples/check.sh holds the tree written
  with its imports, and `--alone` to its bypass.

**Rule lives in:** `GUIDE.md`, The command.
