# `self` names the concrete object for Bend's sugar

`blend-do-self` · maintainer · rev 5f1d86b

**Context.** Bend's `do M<xs.., R>:` desugars by name: each `<-` calls
`M.bind`, each `return` `M.pure` (docs/reviews/Sugar_2026-11-08.md). A
`do` header naming an object passed through Blend as written: no late
binding (an update of `pure` reached no body that used it), no order
(`bind` written below its use failed Bend's check), no use counted, and
no way at all to write the header in an abstract object, which has no
name of its own to write.

**Decision.** The maintainer (2026-11-08): `self` is a word of Blend's,
naming the concrete object an object's definitions are copied into, in
a `do` header: `do self<R>:` is a use of the concrete object's final
`bind` and `pure`, bound late, as a bare name is. Chosen over a header
with no name (`do <R>:`), which would serve `do` alone, a name serving
whatever of Bend's sugar wants one; as glam's `.g` names an object's
`self` by its default `alias self`, an `alias Name` of its own may come
later (`blend-macros.alias`).

Revised (the maintainer, 2026-11-08): Bend's operators too, `(a + b :
T)` calling `T.add` and its kin by name, the review's F4 having been
undesigned rather than declined; `shared` for both, for uniformity and
no surprises; and the sugar's subject latent only where it is `self` or
a nested object, bound late as a dotted name is (`blend-nested-late`),
a top-level object's name plain, left as written for Bend, Blend
refusing it where its members would be written below their use. An
operator Blend does not know, over a latent subject, is an error: Bend
may add operators.

The rest is the agent's:
- A latent subject's name is written as the object's emitted name and
  its uses as references in a comment ending the line; a plain one is
  untouched, its members' order checked at emission (`sg.units`).
- The header's name is written as the object's emitted name, and the
  uses as references in a comment the header's line ends with, `do
  Loud<U32>:  # Loud.bind Loud.pure`, so that Blend orders them before
  the body and counts them as any use, with no line added: the markers
  stay exact.
- `bind` and `pure` reached by a `do` must be `shared`: Bend writes one
  name for every step of the block, so that neither affine nor `copied`
  can be honored. A member that is neither, or missing, is an error at
  the header's line.
- An annotation over a latent subject is read on one line: the
  operators of the parentheses it closes, inner ones without an
  annotation of their own included, as Bend reads them; one whose
  parentheses open on a line before is an error.
- `self` anywhere else is an error. In a module's own definition, `self`
  names nothing, the module being no object (`blend-module-is-bend`).

**Consequences.**
- An abstract object can write a `do` over the monad its concrete
  objects give; a mixin wrapping `_bind` and `_pure` layers an effect
  over its parent's.
- An object that served as a monad by accident, its `bind` and `pure`
  unmarked, now fails until they are marked `shared`.
- Every emitted file with a `do` over an object carries the comment.

**Rule lives in:** `blend.bend`, Objects as monads (`do.rb`) and
Operators over objects; `GUIDE.md`, Objects as monads.
