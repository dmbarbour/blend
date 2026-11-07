# A typed declaration is checked by a witness Bend checks

`blend-declares-witnessed` · maintainer · rev bd20dd9

**Context.** `declare foo` said only that a concrete family must define
`foo`, with no way to say its type, while types may be overridden (the
maintainer, 2026-11-04, `blend-typed-declares`). Blend has no type
checker and adds no Bend logic of its own (`blend-adds-no-bend-logic`).

**Decision.** As planned with the maintainer:
1. `declare def push(st: S(), +x: U32) -> S()`, a header with no body,
   or `declare push(...) -> S()` for short, as `upd` alone is for
   `upd def`; `declare type S: Data`, its kind stated; an untyped
   `declare after` as before.
2. The signature is bound in each concrete object against its own final
   types, so that an overridden type flows into it (Haskell's class
   methods over associated types, Rust's trait methods over `Self::S`),
   fixed where first made: a second declaration of the name below is an
   error, the families varying through their type members.
3. Bend checks it: for each concrete object a witness,
   `def Listed.LAW.push.as_declared(st: Listed.S(), +x: U32) ->
   Listed.S(): Listed.push(st, x)`, or for a kind
   `def Listed.LAW.S.as_declared() -> Data: Listed.S()`, its marker
   naming the declaration, in the module's own file with its laws
   (`blend-laws-in-module`): a witness no `main` reaches is not
   compiled, and makes no second caller (the kernel, 2026-11-06).
   `--verdict` accepts a witness as any total def (tried 2026-11-05).

4. The maintainer (2026-11-05): the name `f.as_declared` is accepted,
   under the object's `LAW` with its laws (`blend-laws-in-module`).
   Two parents each declaring a name conflict, even where their
   declarations agree: introducing a name pins its meaning or purpose,
   and two parents need not mean the same by it; the rule errs on the
   side of caution.

**Consequences.**
- A misfit is Bend's error at the witness, expected and observed types
  printed, found by the gate's proof step, on the witness's one line,
  which where.sh maps to the declaration (`markers.witness`); the samples Blend emits and
  Bend refuses live in `samples/refused/`, held to Bend's output.
- The samples `declares`, `declare-twice`, `declare-no-type`,
  `declare-misfit`, `declare-kind`.

**Rule lives in:** `GUIDE.md`, Types and declarations.
