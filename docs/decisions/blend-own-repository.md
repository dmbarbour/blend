# Blend is a repository of its own

`blend-own-repository` · maintainer · rev 4110220

**Context.** Blend grew inside glam-in-bend, as the vehicle for glam's
kernel (glam-in-bend's `codegen-vehicle`); it is meant to be shared
beyond it (`blend-home`). The maintainer, 2026-11-05: arrange Blend as a
repository, its records, checks and benchmarks with it; then, the empty
repository made, go ahead with a submodule.

**Decision.** Blend is a repository of its own
(github.com/dmbarbour/blend), its history filtered from glam-in-bend's:
its directory's, its records' and its plan's commits, the records and
plan at the paths they had before they moved into it, each commit's
message and trailers kept, and each record's rev mapped to the commit it
became. It holds its code, samples, laws, proofs and mutants, its
benchmarks (`bench/`), its docs (`docs/`), its gate (`check.sh`), its
tools (`scripts/`, copied from glam-in-bend's at the split, Blend's own
since) and its hooks (`.githooks/`). glam-in-bend uses it as a submodule
at its `blend/`, pinned to the commit it was tested with.

**Consequences.**
- A change to Blend is committed and pushed here first; then
  glam-in-bend records the new commit, never before.
- Blend's tools may diverge from glam-in-bend's: a fix wanted in both is
  made in both.
- The analysis store's runs up to 281, which the plan cites, are
  glam-in-bend's store's; Blend's own store begins again.

**Rule lives in:** `AGENTS.md`, Layout and Used by glam-in-bend.
