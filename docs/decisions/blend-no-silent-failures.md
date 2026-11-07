# A failure no law prevents is reported, never silent

`blend-no-silent-failures` · maintainer · rev f269354

**Context.** Two of the copies' fallbacks were silent: a worklist past
its fuel dropped the copies it had not made, which lost an object's
inherited definitions without a word until moving glam's kernel onto
Blend found it (`blend-scale.copies-fuel`); and a member not found was
copied as a placeholder (`NBad`). Proving the copies' laws
(`blend-laws2`) met both: neither was ruled out by a law, and each hid
what the laws were to claim.

**Decision.** The maintainer (2026-11-07): where no law prevents a
failure, Blend reports it as an error, never handles it silently by
dropping work or writing a placeholder. So a worklist past its fuel
(`cp.short`) and a member not found (`copy.of`) are errors. A law
may then claim its property where no error is reported, the guard's
shape (`copies.complete`, `copies.defined`), cheap to prove; a law
that rules the failure out where Blend meets it (`copies.found`, in
the context emission builds) leaves the report in place, and the
guarded law is kept for every other context (the maintainer,
2026-11-07: keep `copies.defined`).

**Consequences.**
- A silent fallback is a bug unless a law shows it unreachable.
- A guarded law comes first and cheaply; the law that the error never
  fires can follow as one of its own.
- With glam's rule that a crash on user input is a bug, Blend's input
  meets an error, never a crash or a quiet loss.

**Rule lives in:** `blend.bend`, Copies (`cp.short`, `copy.of`);
`docs/Proving.md`, "A silent fallback made an error".
