# A path holding a newline is refused

`blend-paths-no-newline` · maintainer · rev d1d2dd3

**Context.** Blend writes a module's file name into lines of what it
emits: the header (`# Written by Blend from FILE`) and each definition's
marker (`# blend: FILE:LINE`), which `where.sh` reads back line by line.
Every path but the ones on the command line comes from a source line,
which holds no newline; a path given on the command line may hold one,
and would then break those lines, a marker's line count with them. Found
sketching the markers' law (`blend-laws.markers.newlines`).

**Decision.** The maintainer (2026-11-05): refuse newlines in file
names. An argument holding a newline, a module's path or the directory
written into, is an error before anything is read or written.

**Consequences.**
- Nothing Blend writes within a line takes a newline from a path, which
  the markers' law can then rely on.
- `samples/check.sh` checks the refusal.

**Rule lives in:** `GUIDE.md`, Limits.
