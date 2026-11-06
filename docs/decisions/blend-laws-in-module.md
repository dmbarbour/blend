# A module's laws and proofs are written into its own file

`blend-laws-in-module` · maintainer · rev bd20dd9

**Context.** Laws and proofs are object members (`blend-object-laws`,
`blend-adds-no-bend-logic`): a law stated in an abstract family holds for
each concrete family, bound to its own finals, and is proved by each, or
once by a proof the family gives, replaced where one needs its own. Bend
pairs a law with a def of its name, in any file, and checks every
definition a run loads, the entry's and its imports', a hub package's
too; `LAWS.bend` and `PROOF.bend` are a project's convention. Blend
first wrote a module's laws and proofs into files apart, `X_LAWS.bend`
and `X_PROOF.bend` (the maintainer, 2026-11-04), which no one importing
the module's code ever checks, a package's least of all; bend-mathlib
keeps each law with its proof, so whoever loads a lemma checks it. Defs
no `main` reaches are not compiled: the kernel given four second
callers no main reaches compiles to the same C, byte for byte. Checking
a module's proofs at each load costs seconds (glam-in-bend's
`docs/reviews/LawsInBend_2026-11-06.md`).

**Decision.** The maintainer (2026-11-06):
1. A module's laws and proofs are written into its own `.bend`, after
   its code, the laws first, then the proofs, each after those it uses:
   an object's law as `Obj.LAW.name`, proved by the def of that name; a
   law outside any object as `LAW.name`; a lemma and a typed
   declaration's witness alike (`Obj.LAW.f.as_declared`). A name the
   code writes with a part `LAW` is an error.
2. `law name:` with its `for` lines and its claim is a member, named as
   a definition is. `proof name(params):` is the proof of the law
   `name`, a member of its own beside the law, emitted as the def Bend
   pairs with it; `upd proof` replaces one inherited, by the rules for
   any definition.
3. A law is a claim, not a definition: code that names one is an error.
   A proof naming its own law names itself, its induction, a prior
   proof's included (any proof of a law serves; binding it late would
   make a prior and the final call each other); naming another law, it
   calls that law's final proof. A proof of no law is an error. A law
   is stated once, never updated: a family wanting a stronger claim
   states a new law (the maintainer, 2026-11-04; `blend-theories` for
   more).
4. The claim stays apart from its proof by inheritance, laws never
   overridden: a law not yet proven is an abstract object's, an abstract
   law its families prove; a concrete object proves every law it has,
   and a top-level law, which cannot be abstract, is proven. Blend
   reports a law unproven there as its own error, before Bend would stop
   every run loading the file.
5. A typed proof, `proof name(params) -> T:`, is a lemma: it states what
   it proves and is named by proofs, never by code. `_name` in a proof,
   of a law (which has no prior), is its proof's prior. A prior no proof
   names is not written; one named is written as a def proving the law
   for the family's finals, its law stated again by the prior's name,
   since Bend types an untyped def by the law of its name. A member keeps
   its kind down the linearization: `upd` updates a definition, `upd
   proof` a proof or a lemma, and neither a law.
6. A project keeps its own `LAWS.bend` and `PROOF.bend` where it wants.

**Consequences.**
- Every run and build loading a module checks its proofs: seconds,
  accepted, incremental checking hoped of Bend later. The programs built
  carry none, Bend compiling what `main` reaches.
- A package's laws travel with its code, checked by whoever imports it,
  its proven laws their lemmas.
- The laws `laws.proven` and `laws.emitted` hold the emitted file free of
  an open law where emission reports no error.
- A proof's name inside Blend is its law's with `#` after it, which no
  name in a body can spell; messages name it `proof name`.
- `scripts/check_laws.py` reads `law` members in `.blend` files as it
  reads `LAWS.bend`, each named by the objects it sits in: changing one
  on main needs its `Law:` trailer. An invalid sample's laws are none.
- Blend's gate rechecks each sample holding a law with `--verdict`;
  import verification reports a laws or proofs file left beside an
  import, written by the Blend before, as no longer emitted.
- The samples `laws`, `laws-imported`, `declares`, `templates`; the
  invalid `law-unproven`, `law-unproven-top`, `law-reserved`,
  `law-reserved-object`,
  `proof-no-law`, `law-named`, `upd-law`, `proof-twice`,
  `upd-proof-undefined`, `law-updated`, `law-shadowed`, `lemma-named`,
  `upd-proof-def`.

**Rule lives in:** `README.md`, The model and What it emits.
