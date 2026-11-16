# Hub candidates

Lemmas Blend's proofs needed, and glam-in-bend's (marked with their
file), that the hub's package
`0x8ae61ec3a6615abd35f196c07232ad28` (bend-mathlib) lacks, stated over
Bend's own types, kept to offer upstream when the maintainer chooses
(the maintainer, 2026-11-06; upstream is commented on only when the
maintainer asks). Each entry names the lemma in `PROOF.bend`, what it
states, and why a proof needed it. Checked against the hub on
2026-11-06: drop an entry when the hub gains it, and add one when a
proof needs a fact of Bend's types the hub lacks.

Left out, as the hub has them under other names: `and_intro`
(`and_eq_true`), `and_l` and `and_r` (`eq_true_of_and_left`,
`eq_true_of_and_right`), `not_true` (`eq_false_of_not_eq_true`),
`u32_eq_of_is_eq` (`string.bend`), `mod_mul` (`add_mul_mod_self_left`),
`xor_refl` (`xor_self`).

## U32

- `u32_is_eq_refl`: `U32.is_eq(a, a) == True`. The hub reaches it only
  through `u32_is_eq_to_nat` and Nat's `is_eq_refl`.
- `u32_is_eq_comm`: `U32.is_eq(a, b) == U32.is_eq(b, a)`.
- `u32_assoc` (with `u32_assoc_n`, `wrap_m`): `U32.add` is associative.
  Base proves `U32.add_comm`, not associativity; proved through
  `to_nat` modulo 2^32, the modulus a variable.
- `u32_zero_r`, `u32_zero_l`: 0 is `U32.add`'s identity.
- `swap4`: `(a + b) + (c + d) == (a + c) + (b + d)` in `U32`.
- `mod10_lt`: `U32.to_nat(U32.mod(n, 10)) < 10`. The hub proves
  `U32.div` (`u32_div_to_nat`) but has no law of `U32.mod`; the general
  forms wanted, `u32_mod_to_nat` (a remainder's value the values'
  remainder) and a bound below the divisor, both follow from the hub's
  own `internal_dm_go`, as `mod10_lt` does.
- `u32_succ_ne`: `U32.is_eq(a + 1, a) == False`, also at 2^32 - 1
  (`sne_k`: below the modulus the sum is itself, at it the remainder 0).
- `digit_ne`, `il_show`: `U32.show`'s characters are never a newline. A
  law of the hub's would say more: each is a digit, `'0'` to `'9'`.

## Nat

- `mod_add_l`: `Nat.mod(Nat.mod(x, n) + y, n) == Nat.mod(x + y, n)`.
- `nat_succ_ne`, `succ_add_ne`: `Nat.is_eq(1n + k + n, n) == False`.
- `uq_nsub`: `Nat.is_lt(y, x) == True` gives `Nat.is_eq(Nat.sub(x, y),
  0n) == False`, a positive difference as a test a match can use. The
  hub's `lt_sub_iff_add_lt` (with 0) has it as `Nat.is_lt(0n, x - y)`.
- `lt0` (glam-in-bend's `glam/PROOF.bend`): `Nat.is_lt(h, 0n) ==
  False`, for a variable `h`: a test such as `Nat.is_lt(1n + g, 1n)`
  stays stuck without it.
- `lt_ne` (glam-in-bend's `glam/PROOF.bend`): `h < m + 1` and
  `Nat.is_eq(h, m) == False` give `h < m`, as tests.

## Bool

- `or_l_true`, `or_r_true`: either side true makes `Bool.or` true, the
  or's introductions (the hub has the and's, `and_eq_true`).
- `not_false`: `b == False` gives `Bool.not(b) == True`.
- `or_false_l`, `or_false_r`: `Bool.or(a, b) == False` gives each side
  false.
- `or_ff` (glam-in-bend's `glam/PROOF.bend`): `a == False` and `b ==
  False` give `Bool.or(a, b) == False`, the converse.
- `or_drop`: an or true with one side false has the other true.
- `or_cases`, `or_map`: a case split on an or that is true.
- `nope`: `False == True` gives any `P == True`.
- `dpu_imp`: `Bool.or(Bool.not(a), b) == True` and `a == True` give
  `b == True`, an implication kept as a `Bool`.
- `dt_or`: in `Bool.or(Bool.or(f, a), g) == True`, `a` traded for an
  `a2` it gives.

## Maybe and List

- `some_inj`: `Some{g} == Some{h}` gives `g == h`.
- `some_none`, `cons_ne_nil`: a constructor's clash refuted.
- `app_nil_l`, `app_nil_r` (stated over `Er`): `List.append(a, b) ==
  Nil` gives `a == Nil` and `b == Nil`, an empty append's sides each
  empty; with `er_cons`, a `Con` is no `Nil`. The hub has `append_nil`
  and `nil_append`, the converse direction.

## Lists of Nat

- `ph` (glam-in-bend's `glam/PROOF.bend`), the pigeonhole: a list of
  `Nat`s pairwise distinct (`nodupN`) and each below `n` (`allLt`) is
  no longer than `n`. Needed to bound a ring's members by the heap's
  words, each member's link word in a slot of its own, so that a walk
  fuelled by the heap's size finishes; the free list's exactness will
  want it too. With its parts: `memN`, `nodupN`, `allLt`, `removeN`
  (the list without a value); `rm_len` (removing from a list without
  duplicates shortens it by one at most), `rm_nodup` (and keeps it
  without), `rm_lt` (all below `m + 1`, `m` removed, all below `m`).
  The hub has no membership, no duplicate-freedom and no removal over
  lists; stated over any type with a test of equality, it would serve
  more.
