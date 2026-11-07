# Inheritance linearized by C3, an error where no order exists

`blend-c3` · maintainer · rev 94208d4

**Context.** An object may name several parents, each linearized in its
turn, and its definitions apply after theirs in the order the
linearization gives (`prior`: the next object's definition). Two
parents' linearizations, and the object's own list of parents, may order
the same objects differently; some such orders cannot be reconciled.

**Decision.** The maintainer (2026-11-04): inheritance is linearized by
C3, as glam's is: an object, then the merge of its parents'
linearizations and its list of parents, each turn taking the first head
in no list's tail. C3 reports an error if there is no valid
linearization, never an order that breaks one it merges.

**Consequences.**
- A linearization begins with its object, keeps each parent's
  linearization and the parents' list in order, and holds each object
  once; where no order does, the object's error names the lists left.
- The laws `c3.sound`, `c3.complete` and `c3.first` hold the merge to
  this (`blend-laws.c3`).

**Rule lives in:** `GUIDE.md`, Objects.
