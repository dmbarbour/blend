# Reviews

A review checks work against intent: a design, a plan's steps, a subsystem.
It lists findings, each with a stable ID (`F1`, `F2`, …; write
`<Review> F3` where ambiguous) and a verdict. These are glam-in-bend's
rules for reviews, which Blend keeps (`blend-own-repository`).

- **Quote what you find.** A finding cites the text or code it is about,
  with its location. A claim relayed from another reviewer or agent is
  checked against the source before it is reported.
- **Small fixes go in the review.** A finding may be fixed in the commit
  that records it, or by follow-ups citing its ID. Work that needs steps of
  its own becomes a plan.
- **Files and retirement follow [plans](../plans/README.md):**
  `docs/reviews/<Topic>_<YYYY-MM-DD>.md`, listed below while active, and
  retired by extracting decisions and removing references, then deleted
  with its last commit listed.

## Active Reviews

- [`Sugar_2026-11-08.md`](Sugar_2026-11-08.md): Bend's name-directed
  sugar (`do M<..>:`, `(a + b : T)`) over Blend's objects: what Bend
  does, what Blend misses today, and the shape of a fix.

## Retired

None yet.
