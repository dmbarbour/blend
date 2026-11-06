# A module's laws and proofs are written into its own file

`blend-laws-in-module` · maintainer · rev 9402c1d

**Context.** `blend-proofs-beside-code` wrote a module's laws and proofs
into files apart from its code, `X_LAWS.bend` and `X_PROOF.bend`, after
Bend's `LAWS.bend` and `PROOF.bend`. Those are a project's convention:
Bend checks every definition a run loads, the entry's and its imports',
a hub package's too, and a law is a type proved by a def of its name
wherever it sits. Laws kept apart are checked by no one who imports the
module's code, a package's least of all; bend-mathlib keeps each law
with its proof, so whoever loads a lemma checks it. Defs no `main`
reaches are not compiled: the kernel given four second callers no main
reaches compiles to the same C, byte for byte. Checking a module's
proofs at each load costs seconds (glam-in-bend's
`docs/reviews/LawsInBend_2026-11-06.md`).

**Decision.** The maintainer (2026-11-06):
- A module's laws and proofs are written into its own `.bend`: an
  object's law as `Obj.LAW.name`, proved by the def of that name; a law
  outside any object as `LAW.name`. A typed declaration's witness too.
- The claim stays apart from its proof by inheritance, laws never
  overridden: a law not yet proven is an abstract object's, an abstract
  law its families prove; a concrete object proves every law it has,
  and a top-level law, which cannot be abstract, is proven. Blend
  reports a law unproven there as its own error, before Bend would stop
  every run loading the file.
- A project keeps its own `LAWS.bend` and `PROOF.bend` where it wants.

**Consequences.**
- Every run and build loading a module checks its proofs: seconds,
  accepted, incremental checking hoped of Bend later.
- A package's laws travel with its code, checked by whoever imports it,
  its proven laws their lemmas.
- The emission's files for laws and proofs, their modes and their
  aliases (`Blend_0`, `Blend_Laws`) go, and Blend's laws stated over
  them are restated, each with the maintainer's approval.
- Replaces `blend-proofs-beside-code` once built (`blend-module-laws` in
  `docs/plans/Blend_2026-11-04.md`); until then the code follows that
  record.

**Rule lives in:** `docs/plans/Blend_2026-11-04.md`, `blend-module-laws`,
until built; then `README.md`, Laws and proofs.
