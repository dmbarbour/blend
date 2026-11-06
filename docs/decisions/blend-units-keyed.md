# The units' table keys each entry by its position

`blend-units-keyed` · maintainer · rev cedf111

**Context.** Emission reads every unit through a table on the units'
positions (`pt.of`, a hash trie as deep as the units' count has bits),
and the laws speak of the units' list. Joining them (`blend-laws.positions`)
needs that the table's lookup at i finds the list's entry i. As built,
that rests on the trie's path following the key's low bits, a proof of
shifts and masks against the key's value, which the hub's `U32` laws do
not reach. The table proved already (`Pw`, `pw_get`) costs 11 to 27% of
the instructions, its 32 levels against the trie's dozen.

**Decision.** The maintainer (2026-11-06): store each entry with its
position, and have a lookup compare it (`Pk`). The table's type changes
from `Ht<Un>` to `Ht<Pk<Un>>`, in the code and in the six laws that
quantify over a table (`mults.uses`, `mults.walked`, `sharing.final`,
`sharing.copied`, `sharing.once`, `sharing.affine`): their claims
unchanged, the type of one variable each.

**Consequences.**
- The positional law is a map's: a put at another key leaves a lookup
  as it was, whatever leaf it lands in, so no arithmetic of the trie's
  path is needed.
- A lookup compares one key more; measured where it lands
  (`blend-laws.positions`).

**Rule lives in:** `blend.bend`, Definitions (`pt.of`, `pt.at`).
