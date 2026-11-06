# A Blend file's imports are local, or a package's

`blend-imports-local` · maintainer · rev d1d39c7

**Context.** Bend lets a local import climb with `../` and name a file by
`/`; a package's root is its entry's directory, and `--publish` refuses
a file outside it. glam rejects even `../`, so that every directory can
be shared as a package (the maintainer, 2026-11-06). Blend emits each
module's `.bend` beside its `.blend`, and the root's file re-imports
what the bodies it copies name; a path that climbs, or one Blend took
for local, makes that tree hard to reason about: a package's import
reached through a copy was written as `./lib/pkg@1.0.0.0/...`.

**Decision.** The maintainer (2026-11-06): an import in a `.blend` file,
of a `.blend` or a `.bend` file, is local: plain names (letters,
digits, `_` and `-`) led by `./` at most, never `../` or `/`. Or it
is a package's on Bend's hub, `0x<hash>/...` or `<name>@<version>/...`,
passed to Bend as written, re-imported as written, Bend's to fetch and
check; importing a package's Blend files is not supported yet
(`blend-packages`).

**Consequences.**
- A directory holds every file its modules import, so it can be shared
  as a package, and every module a root reaches sits beneath it.
- `import.plain` tests that a path stays within its directory
  (`path.down`) beside its plain names: the boundary the law
  `imports.local` reads; `imports.package` holds a package's path as
  written through the root's re-imports.
- Blend refuses some paths Bend takes.

**Rule lives in:** `README.md`, Imports.
