# A dotted name through a nested object binds late

`blend-nested-late` · maintainer · rev f7beb60

**Context.** A nested object is a member: a family gets its own,
made for it (`blend-nested`, `blend-frozen-host`). But a dotted name,
`Inner.k`, was bound where it was written, from the defining object
outward: in `Outer2 extends Outer`, the body `Outer.f` calling `Inner.k`
called `Outer.Inner.k` in Outer2's copy too, deaf to `extend Inner`, and
an abstract object could not call into a nested object its families
fill in at all, the name binding to its own abstract one. Found
2026-11-08, weighing Bend's sugar over objects.

**Decision.** The maintainer (2026-11-08): nested objects bind late; the
early binding made them nearly pointless, and late binding was the
intention all along. The rest is the agent's:
- A dotted name's object is looked for among the concrete object's own
  nested objects first (`look.own`), then as before, from where the name
  is written, outward (`look.obj`): a bare name's order, the concrete
  object's own members, then the scopes the name is written in.
- So a top-level object, the module's member, is the same for every
  family; and a body inherited by a path keeps the hosts it was bound
  to, `blend-frozen-host`'s third rule: the lookup never walks outward
  from the concrete object.

**Consequences.**
- `extend Inner` in a family reaches every body the family inherits
  that names `Inner`, and an abstract object can write against an
  abstract nested object its families fill in.
- A name a family's own nested object shares with a top-level object
  names the nested one in that family's copies, as a bare name would.

**Rule lives in:** `blend.bend`, A name bound (`look.late`); `GUIDE.md`,
Objects and Nested objects. Samples `nested-late`, `nested-frozen`.
