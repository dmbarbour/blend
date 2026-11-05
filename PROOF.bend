# Blend's own proofs, of the laws LAWS.bend states.
#
# Lessons, for the next proof (docs/BendIssues.md has Bend's side):
# - A byte's match (`case 46:` ... `case _:`) leaves a proof stuck, a
#   U32 being a word of bits: code a law follows tests its bytes
#   (`U32.is_eq(h, 46)`) and branches on the Bool, in `when` or in a
#   named helper matching its Bool parameters (`rr.mark.k`); a class of
#   bytes is a datatype (`Cl`), its tests Bools.
# - A recursive proof never matches a computed value: a non-recursive
#   step lemma takes the Bool as a parameter, with both induction
#   hypotheses, and splits it (`parts_step`, `while_step_s`); Bend has
#   no mutual recursion, so the split lives in the step, the recursion in
#   the caller.
# - A lemma's type names a `when`'s branches through a helper def that
#   mirrors them (`while_k`, `lines_k`): Bend infers no lambda.
# - Lemmas run simple == complex, so that `%e : P` (the goal is P with
#   e's right side, and becomes P with its left) rewrites the complex form
#   away; the hub's lemmas run the other way, so wrap them in
#   `Equal.sym` once (`assoc_r`, `rev_snoc`).
# - A result read twice is Data, read by projections (`Rn`, `rn.xs`), not
#   destructured in a lambda (`on.rn`), which sticks a proof.
# - A bound of 2^32 is reasoned under a variable N with {N == 2^32}, the
#   power met only against a symbolic count or where both forms match
#   exactly (`to32`, `top_bound`): Bend unfolds the power otherwise, and
#   its checker overflows.
# - Templates prove as code does: a proof def may take `~p` (`while_s`).
# - Termination by a potential (`pot`): each step lowers it (`step_desc`),
#   the fuel is its value at the start (`fuel_pot`), and induction on the
#   fuel ends the walk (`ends`). Each unit's calls count once, by its
#   position (`taken`, `psw_drop`), so that the fuel is linear.
# - A fast walk proved against the walk (`order.fast`): a state lifted
#   with the tries its lists make, a step from it the lifted step
#   (`step_lift`); the tries on U32's own bits (`has_put`, `put_comm`).
# - The dispositions (`mults.uses`): a specification sharing `mult.of`,
#   the uses waiting characterized after the units taken (`pa_at`), the
#   induction's order the specification's reversal's accumulator.
# - The names check (`emit.unique`): the hash trie's bit tested and
#   decided by helpers that call nothing (`ht.pick`, `ht.join`), the
#   recursion on fuel, so that a step lemma splits the test
#   (`leaf_put.k`, `mono.k`) and the code pays a little, where a `when`'s
#   closures cost a fifth; the check's step mirrored (`ers_k`) with its
#   error's text, a `Con` against `Nil` refuted through the mirror.
# - C3 (`c3.sound`, `c3.complete`): the merge's accumulator peeled off
#   by a twin without it (`mrest`, `merge_acc`); completeness by
#   induction on a witness order, never a cycle (`good_of`); a lemma's
#   mutually recursive partner taken as a function (`sub_weak`).
# - The writer's counters (`sharing.counts`): each step's effect on one
#   counter, for any text before it (`cy`, `keep`); U32 sums reassociated
#   through to_nat (`u32_assoc`), the modulus a variable (`wrap_m`).
# - The final dispositions (`sharing.final`): a unit's set at its turn
#   alone (`frozen`), its users' before it (`at_turn`); joined with the
#   writer's counters (`sharing.copied`) through `mults.uses`.
# - Mutate the code after a proof passes: a law that survives a mutation
#   claims less than meant.

import Base
import ./LAWS.bend as Laws
import ./blend.bend as B
import 0x8ae61ec3a6615abd35f196c07232ad28/nat.bend as MNat
import 0x8ae61ec3a6615abd35f196c07232ad28/u32.bend as MU
import 0x8ae61ec3a6615abd35f196c07232ad28/bool.bend as MB
import 0x8ae61ec3a6615abd35f196c07232ad28/list.bend as ML
import 0x8ae61ec3a6615abd35f196c07232ad28/equal.bend as ME

# Bytes
# -----

def u32_is_eq_refl(+a: U32) -> {U32.is_eq(a, a) == True{} : Bool}:
  %MU.u32_is_eq_to_nat_sym(a, a) : {_ == True{} : Bool}
  MNat.is_eq_refl(U32.to_nat(a))

def u32_nat_is_eq(+a: U32, +b: U32, h: {U32.is_eq(a, b) == True{} : Bool}) -> {Nat.is_eq(U32.to_nat(a), U32.to_nat(b)) == True{} : Bool}:
  %MU.u32_is_eq_to_nat(a, b) : {_ == True{} : Bool}
  h

def u32_eq_of_is_eq(+a: U32, +b: U32, h: {U32.is_eq(a, b) == True{} : Bool}) -> {a == b : U32}:
  MU.u32_to_nat_inj(a, b, MNat.eq_of_is_eq(U32.to_nat(a), U32.to_nat(b), u32_nat_is_eq(a, b, h)))

# Names
# -----

# by induction over both names: the heads equal by U32.is_eq, the tails by
# the hypothesis; a name and a longer one are never the same
def Laws.names.same_eq(a, b, h):
  match a:
    case Nil{}:
      match b:
        case Nil{}:
          {==}
        case Con{bh, bt}:
          Empty.absurd({Nil{} == Con{bh, bt} : List<&2, U32>}, MB.false_ne_true()(h))
    case Con{ah, at}:
      match b:
        case Nil{}:
          Empty.absurd({Con{ah, at} == Nil{} : List<&2, U32>}, MB.false_ne_true()(h))
        case Con{bh, bt}:
          %u32_eq_of_is_eq(ah, bh, MB.eq_true_of_and_left(U32.is_eq(ah, bh), B.same(at, bt), h)) : {Con{ah, at} == Con{_, bt} : List<&2, U32>}
          %Laws.names.same_eq(at, bt, MB.eq_true_of_and_right(U32.is_eq(ah, bh), B.same(at, bt), h)) : {Con{ah, at} == Con{ah, _} : List<&2, U32>}
          {==}

def Laws.names.same_refl(a):
  match a:
    case Nil{}:
      {==}
    case Con{ah, at}:
      %Equal.sym(Bool, U32.is_eq(ah, ah), True{}, u32_is_eq_refl(ah)) : {Bool.and(_, B.same(at, at)) == True{} : Bool}
      Laws.names.same_refl(at)

# Dotted names
# ------------
#
# parts.go splits a name at its dots, the part so far reversed in cur and
# the parts done reversed in out; its spec: the parts done, each with its
# dot (dp), then the part so far, then what is left, are what the parts
# it returns join to. The lemmas run simple == complex, so that a
# rewrite turns the complex form in a goal into the simple.

# parts in order, each followed by its dot
def dp(ps: List<&2, List<&2, U32>>) -> List<&2, U32>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{p, r}:
      List.append(&2, U32, p, Con{46, dp(r)})

def assoc_r(+a: List<&2, U32>, +b: List<&2, U32>, +c: List<&2, U32>) ->
    {List.append(&2, U32, a, List.append(&2, U32, b, c)) == List.append(&2, U32, List.append(&2, U32, a, b), c) : List<&2, U32>}:
  Equal.sym(List<&2, U32>, List.append(&2, U32, List.append(&2, U32, a, b), c), List.append(&2, U32, a, List.append(&2, U32, b, c)),
    ML.append_assoc(&2, U32, a, b, c))

def rev_snoc(+xs: List<&2, U32>, +y: U32) -> {List.append(&2, U32, List.reverse(&2, U32, xs), [y]) == List.reverse.go(&2, U32, xs, [y]) : List<&2, U32>}:
  Equal.sym(List<&2, U32>, List.reverse.go(&2, U32, xs, [y]), List.append(&2, U32, List.reverse(&2, U32, xs), [y]),
    ML.reverse_go_spec(&2, U32, xs, [y]))

def revs_snoc(+xs: List<&2, List<&2, U32>>, +y: List<&2, U32>) ->
    {List.append(&2, List<&2, U32>, List.reverse(&2, List<&2, U32>, xs), [y]) == List.reverse.go(&2, List<&2, U32>, xs, [y]) : List<&2, List<&2, U32>>}:
  Equal.sym(List<&2, List<&2, U32>>, List.reverse.go(&2, List<&2, U32>, xs, [y]), List.append(&2, List<&2, U32>, List.reverse(&2, List<&2, U32>, xs), [y]),
    ML.reverse_go_spec(&2, List<&2, U32>, xs, [y]))

# a part appended: its dot after it
def dp_snoc(ps: List<&2, List<&2, U32>>, +x: List<&2, U32>) ->
    {List.append(&2, U32, dp(ps), List.append(&2, U32, x, [46])) == dp(List.append(&2, List<&2, U32>, ps, [x])) : List<&2, U32>}:
  match ps:
    case Nil{}:
      {==}
    case Con{+p, +r}:
      %dp_snoc(r, x) : {List.append(&2, U32, List.append(&2, U32, p, Con{46, dp(r)}), List.append(&2, U32, x, [46])) == List.append(&2, U32, p, Con{46, _}) : List<&2, U32>}
      ML.append_assoc(&2, U32, p, Con{46, dp(r)}, List.append(&2, U32, x, [46]))

# a part appended, the parts joined
def dots_snoc(ps: List<&2, List<&2, U32>>, +c: List<&2, U32>) ->
    {List.append(&2, U32, dp(ps), c) == B.dots(List.append(&2, List<&2, U32>, ps, [c])) : List<&2, U32>}:
  match ps:
    case Nil{}:
      {==}
    case Con{+p, r}:
      match r:
        case Nil{}:
          ML.append_assoc(&2, U32, p, [46], c)
        case Con{+q, +r2}:
          %dots_snoc(Con{q, r2}, c) : {List.append(&2, U32, List.append(&2, U32, p, Con{46, dp(Con{q, r2})}), c) == List.append(&2, U32, p, Con{46, _}) : List<&2, U32>}
          ML.append_assoc(&2, U32, p, Con{46, dp(Con{q, r2})}, c)

# a byte after the part so far, a dot or not, b its test (the step's two
# hypotheses, for the tail after a dot and after another byte)
def parts_step(+h: U32, +t: List<&2, U32>, +cur: List<&2, U32>, +out: List<&2, List<&2, U32>>, b: Bool, +e: {b == U32.is_eq(h, 46) : Bool},
    ih1: {List.append(&2, U32, dp(List.reverse(&2, List<&2, U32>, Con{List.reverse(&2, U32, cur), out})), List.append(&2, U32, List.reverse(&2, U32, Nil{}), t)) ==
      B.dots(B.parts.go(t, Nil{}, Con{List.reverse(&2, U32, cur), out})) : List<&2, U32>},
    ih2: {List.append(&2, U32, dp(List.reverse(&2, List<&2, U32>, out)), List.append(&2, U32, List.reverse(&2, U32, Con{h, cur}), t)) ==
      B.dots(B.parts.go(t, Con{h, cur}, out)) : List<&2, U32>}) ->
    {List.append(&2, U32, dp(List.reverse(&2, List<&2, U32>, out)), List.append(&2, U32, List.reverse(&2, U32, cur), Con{h, t})) ==
      B.dots(B.when(List<&2, List<&2, U32>>, b, u => B.parts.go(t, Nil{}, Con{List.reverse(&2, U32, cur), out}), u => B.parts.go(t, Con{h, cur}, out))) : List<&2, U32>}:
  match b:
    case True{}:
      %Equal.sym(U32, h, 46, u32_eq_of_is_eq(h, 46, Equal.sym(Bool, True{}, U32.is_eq(h, 46), e))) :
        {List.append(&2, U32, dp(List.reverse(&2, List<&2, U32>, out)), List.append(&2, U32, List.reverse(&2, U32, cur), Con{_, t})) ==
          B.dots(B.parts.go(t, Nil{}, Con{List.reverse(&2, U32, cur), out})) : List<&2, U32>}
      %ih1 : {List.append(&2, U32, dp(List.reverse(&2, List<&2, U32>, out)), List.append(&2, U32, List.reverse(&2, U32, cur), Con{46, t})) == _ : List<&2, U32>}
      %revs_snoc(out, List.reverse(&2, U32, cur)) :
        {List.append(&2, U32, dp(List.reverse(&2, List<&2, U32>, out)), List.append(&2, U32, List.reverse(&2, U32, cur), Con{46, t})) == List.append(&2, U32, dp(_), t) : List<&2, U32>}
      %dp_snoc(List.reverse(&2, List<&2, U32>, out), List.reverse(&2, U32, cur)) :
        {List.append(&2, U32, dp(List.reverse(&2, List<&2, U32>, out)), List.append(&2, U32, List.reverse(&2, U32, cur), Con{46, t})) == List.append(&2, U32, _, t) : List<&2, U32>}
      %assoc_r(dp(List.reverse(&2, List<&2, U32>, out)), List.append(&2, U32, List.reverse(&2, U32, cur), [46]), t) :
        {List.append(&2, U32, dp(List.reverse(&2, List<&2, U32>, out)), List.append(&2, U32, List.reverse(&2, U32, cur), Con{46, t})) == _ : List<&2, U32>}
      %assoc_r(List.reverse(&2, U32, cur), [46], t) :
        {List.append(&2, U32, dp(List.reverse(&2, List<&2, U32>, out)), List.append(&2, U32, List.reverse(&2, U32, cur), Con{46, t})) ==
          List.append(&2, U32, dp(List.reverse(&2, List<&2, U32>, out)), _) : List<&2, U32>}
      {==}
    case False{}:
      %ih2 : {List.append(&2, U32, dp(List.reverse(&2, List<&2, U32>, out)), List.append(&2, U32, List.reverse(&2, U32, cur), Con{h, t})) == _ : List<&2, U32>}
      %rev_snoc(cur, h) :
        {List.append(&2, U32, dp(List.reverse(&2, List<&2, U32>, out)), List.append(&2, U32, List.reverse(&2, U32, cur), Con{h, t})) ==
          List.append(&2, U32, dp(List.reverse(&2, List<&2, U32>, out)), List.append(&2, U32, _, t)) : List<&2, U32>}
      %assoc_r(List.reverse(&2, U32, cur), [h], t) :
        {List.append(&2, U32, dp(List.reverse(&2, List<&2, U32>, out)), List.append(&2, U32, List.reverse(&2, U32, cur), Con{h, t})) ==
          List.append(&2, U32, dp(List.reverse(&2, List<&2, U32>, out)), _) : List<&2, U32>}
      {==}

# parts.go's spec, by induction over what is left
def parts_spec(xs: List<&2, U32>, +cur: List<&2, U32>, +out: List<&2, List<&2, U32>>) ->
    {List.append(&2, U32, dp(List.reverse(&2, List<&2, U32>, out)), List.append(&2, U32, List.reverse(&2, U32, cur), xs)) == B.dots(B.parts.go(xs, cur, out)) : List<&2, U32>}:
  match xs:
    case Nil{}:
      %revs_snoc(out, List.reverse(&2, U32, cur)) :
        {List.append(&2, U32, dp(List.reverse(&2, List<&2, U32>, out)), List.append(&2, U32, List.reverse(&2, U32, cur), Nil{})) == B.dots(_) : List<&2, U32>}
      %dots_snoc(List.reverse(&2, List<&2, U32>, out), List.reverse(&2, U32, cur)) :
        {List.append(&2, U32, dp(List.reverse(&2, List<&2, U32>, out)), List.append(&2, U32, List.reverse(&2, U32, cur), Nil{})) == _ : List<&2, U32>}
      %ML.append_nil(&2, U32, List.reverse(&2, U32, cur)) :
        {List.append(&2, U32, dp(List.reverse(&2, List<&2, U32>, out)), List.append(&2, U32, List.reverse(&2, U32, cur), Nil{})) ==
          List.append(&2, U32, dp(List.reverse(&2, List<&2, U32>, out)), _) : List<&2, U32>}
      {==}
    case Con{+h, +t}:
      parts_step(h, t, cur, out, U32.is_eq(h, 46), {==}, parts_spec(t, Nil{}, Con{List.reverse(&2, U32, cur), out}), parts_spec(t, Con{h, cur}, out))

def Laws.names.dots_parts(x):
  Equal.sym(List<&2, U32>, x, B.dots(B.parts(x)), parts_spec(x, Nil{}, Nil{}))

# Locals
# ------

def list_disc(xs: List<&2, U32>) -> Type:
  match xs:
    case Nil{}:
      Unit
    case Con{c, cs}:
      Empty

def cons_ne_nil(+c: U32, +cs: List<&2, U32>, e: {Con{c, cs} == Nil{} : List<&2, U32>}) -> Empty:
  %Equal.sym(List<&2, U32>, Con{c, cs}, Nil{}, e) : list_disc(_)
  Unit{}

def Laws.locals.not_name(cx, o, q, locals, t, no, h):
  match t:
    case B.TName{x}:
      match x:
        case Nil{}:
          {==}
        case Con{c, cs}:
          Empty.absurd({B.rr.of(cx, o, q, locals, B.TName{Con{c, cs}}, no) == B.rr.tok(B.TName{Con{c, cs}}) : B.Rr}, cons_ne_nil(c, cs, h))
    case B.TNum{x}:
      {==}
    case B.TStr{x}:
      {==}
    case B.TCom{x}:
      {==}
    case B.TSp{x}:
      {==}
    case B.TSym{c}:
      {==}

# the middle of three, true, makes them true
def or3_mid(+a: Bool, +b: Bool, +c: Bool, e: {b == True{} : Bool}) -> {Bool.or(Bool.or(a, b), c) == True{} : Bool}:
  %Equal.sym(Bool, b, True{}, e) : {Bool.or(Bool.or(a, _), c) == True{} : Bool}
  %MB.or_true_sym(a) : {Bool.or(_, c) == True{} : Bool}
  {==}

# a local, found, is kept: rr.plain's test and rr.under's, each a Bool
# the hypothesis says is True
def plain_kept(+local: Bool, +e: {local == True{} : Bool}, +cx: B.Cx, +o: U32, +q: U32, +mark: U32, +n: List<&2, U32>, +t: B.Tok, +no: U32) ->
    {B.rr.plain.k(local, cx, o, q, mark, n, t, no) == B.rr.tok(t) : B.Rr}:
  match local:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({B.rr.plain.k(False{}, cx, o, q, mark, n, t, no) == B.rr.tok(t) : B.Rr}, MB.false_ne_true()(e))

def under_kept(+local: Bool, +e: {local == True{} : Bool}, +cx: B.Cx, +o: U32, +q: U32, +r: List<&2, U32>, +t: B.Tok, +no: U32) ->
    {B.rr.under(local, cx, o, q, r, t, no) == B.rr.tok(t) : B.Rr}:
  match local:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({B.rr.under(False{}, cx, o, q, r, t, no) == B.rr.tok(t) : B.Rr}, MB.false_ne_true()(e))

# a plain name or `_n`, its first byte's tests split: `^` and `~` false
# by the hypotheses, `_` either way
def mark_kept(+up: Bool, a: {up == False{} : Bool}, +tpl: Bool, b: {tpl == False{} : Bool}, +under: Bool,
    +cx: B.Cx, +o: U32, +q: U32, +locals: List<&2, List<&2, U32>>, +h: U32, +r: List<&2, U32>, +no: U32,
    +l: {B.names.has(locals, Con{h, r}) == True{} : Bool}) ->
    {B.rr.mark.k(up, tpl, under, cx, o, q, locals, h, r, B.TName{Con{h, r}}, no) == B.rr.tok(B.TName{Con{h, r}}) : B.Rr}:
  match up:
    case True{}:
      Empty.absurd({B.rr.mark.k(True{}, tpl, under, cx, o, q, locals, h, r, B.TName{Con{h, r}}, no) == B.rr.tok(B.TName{Con{h, r}}) : B.Rr},
        MB.true_ne_false()(a))
    case False{}:
      match tpl:
        case True{}:
          Empty.absurd({B.rr.mark.k(False{}, True{}, under, cx, o, q, locals, h, r, B.TName{Con{h, r}}, no) == B.rr.tok(B.TName{Con{h, r}}) : B.Rr},
            MB.true_ne_false()(b))
        case False{}:
          match under:
            case True{}:
              under_kept(Bool.or(Bool.or(B.blank(r), B.names.has(locals, Con{h, r})), B.is.root(B.cx.obs(cx), o)),
                or3_mid(B.blank(r), B.names.has(locals, Con{h, r}), B.is.root(B.cx.obs(cx), o), l), cx, o, q, r, B.TName{Con{h, r}}, no)
            case False{}:
              plain_kept(B.names.has(locals, Con{h, r}), l, cx, o, q, 0, Con{h, r}, B.TName{Con{h, r}}, no)

def Laws.locals.kept(cx, o, q, locals, h, r, no, a, b, l):
  mark_kept(U32.is_eq(h, 94), a, U32.is_eq(h, 126), b, U32.is_eq(h, 95), cx, o, q, locals, h, r, no, l)

def Laws.locals.template(cx, o, q, locals, r, no, l):
  plain_kept(B.names.has(locals, r), l, cx, o, q, 126, r, B.TName{Con{126, r}}, no)

# Tokens
# ------
#
# toks.go takes a token a turn, the fuel the line's length, the classes
# in step with the bytes: what the tokens so far spell, then what is
# left, is what the tokens it returns spell. A run's lemmas: what it took
# reversed back, then what it left, is what it was given after what it
# had (spelt); its classes stay in step (len); it leaves no more than it
# was given (le). The run's choice, a Bool, is split by a step lemma.

def len_classes(xs: List<&2, U32>) -> {List.length(&2, B.Cl, B.classes(xs)) == List.length(&2, U32, xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      ME.cong_succ(List.length(&2, B.Cl, B.classes(t)), List.length(&2, U32, t), len_classes(t))

def text_append(a: List<&2, B.Tok>, +b: List<&2, B.Tok>) ->
    {List.append(&2, U32, B.toks.text(a), B.toks.text(b)) == B.toks.text(List.append(&2, B.Tok, a, b)) : List<&2, U32>}:
  match a:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      %text_append(r, b) : {List.append(&2, U32, List.append(&2, U32, B.tok.bytes(x), B.toks.text(r)), B.toks.text(b)) == List.append(&2, U32, B.tok.bytes(x), _) : List<&2, U32>}
      ML.append_assoc(&2, U32, B.tok.bytes(x), B.toks.text(r), B.toks.text(b))

def text_snoc(+out: List<&2, B.Tok>, +x: B.Tok) ->
    {List.append(&2, U32, B.toks.text(List.reverse(&2, B.Tok, out)), B.tok.bytes(x)) == B.toks.text(List.reverse(&2, B.Tok, Con{x, out})) : List<&2, U32>}:
  %Equal.sym(List<&2, B.Tok>, List.reverse.go(&2, B.Tok, out, [x]), List.append(&2, B.Tok, List.reverse(&2, B.Tok, out), [x]), ML.reverse_go_spec(&2, B.Tok, out, [x])) :
    {List.append(&2, U32, B.toks.text(List.reverse(&2, B.Tok, out)), B.tok.bytes(x)) == B.toks.text(_) : List<&2, U32>}
  %text_append(List.reverse(&2, B.Tok, out), [x]) :
    {List.append(&2, U32, B.toks.text(List.reverse(&2, B.Tok, out)), B.tok.bytes(x)) == _ : List<&2, U32>}
  %ML.append_nil(&2, U32, B.tok.bytes(x)) :
    {List.append(&2, U32, B.toks.text(List.reverse(&2, B.Tok, out)), _) == List.append(&2, U32, B.toks.text(List.reverse(&2, B.Tok, out)), List.append(&2, U32, B.tok.bytes(x), Nil{})) : List<&2, U32>}
  {==}

# what a run spells
def spelt(+r: B.Rn) -> List<&2, U32>:
  List.append(&2, U32, List.reverse(&2, U32, B.rn.acc(r)), B.rn.xs(r))

# a byte taken after acc: what is left after it, so spelt
def took(+acc: List<&2, U32>, +h: U32, +t: List<&2, U32>) ->
    {List.append(&2, U32, List.reverse(&2, U32, acc), Con{h, t}) == List.append(&2, U32, List.reverse(&2, U32, Con{h, acc}), t) : List<&2, U32>}:
  %rev_snoc(acc, h) : {List.append(&2, U32, List.reverse(&2, U32, acc), Con{h, t}) == List.append(&2, U32, _, t) : List<&2, U32>}
  %assoc_r(List.reverse(&2, U32, acc), [h], t) : {List.append(&2, U32, List.reverse(&2, U32, acc), Con{h, t}) == _ : List<&2, U32>}
  {==}

# Runs while a class test holds

def while_k(~p: B.Cl -> Bool, +h: U32, +t: List<&2, U32>, +c: B.Cl, +ct: List<&2, B.Cl>, +acc: List<&2, U32>, +b: Bool) -> B.Rn:
  B.when(B.Rn, b, u => B.run.while(~p, t, ct, Con{h, acc}), u => B.Rn{acc, Con{h, t}, Con{c, ct}})

def while_step_s(~p: B.Cl -> Bool, +h: U32, +t: List<&2, U32>, +c: B.Cl, +ct: List<&2, B.Cl>, +acc: List<&2, U32>, b: Bool,
    ih: {List.append(&2, U32, List.reverse(&2, U32, Con{h, acc}), t) == spelt(B.run.while(~p, t, ct, Con{h, acc})) : List<&2, U32>}) ->
    {List.append(&2, U32, List.reverse(&2, U32, acc), Con{h, t}) == spelt(while_k(~p, h, t, c, ct, acc, b)) : List<&2, U32>}:
  match b:
    case True{}:
      Equal.trans(List<&2, U32>, List.append(&2, U32, List.reverse(&2, U32, acc), Con{h, t}), List.append(&2, U32, List.reverse(&2, U32, Con{h, acc}), t),
        spelt(B.run.while(~p, t, ct, Con{h, acc})), took(acc, h, t), ih)
    case False{}:
      {==}

def while_s(~p: B.Cl -> Bool, t: List<&2, U32>, ct: List<&2, B.Cl>, +acc: List<&2, U32>, +al: {List.length(&2, B.Cl, ct) == List.length(&2, U32, t) : Nat}) ->
    {List.append(&2, U32, List.reverse(&2, U32, acc), t) == spelt(B.run.while(~p, t, ct, acc)) : List<&2, U32>}:
  match t:
    case Nil{}:
      match ct:
        case Nil{}:
          {==}
        case Con{+c, +ct2}:
          Empty.absurd({List.append(&2, U32, List.reverse(&2, U32, acc), Nil{}) == spelt(B.run.while(~p, Nil{}, Con{c, ct2}, acc)) : List<&2, U32>},
            MNat.succ_ne_zero(List.length(&2, B.Cl, ct2))(al))
    case Con{+h, +t2}:
      match ct:
        case Nil{}:
          Empty.absurd({List.append(&2, U32, List.reverse(&2, U32, acc), Con{h, t2}) == spelt(B.run.while(~p, Con{h, t2}, Nil{}, acc)) : List<&2, U32>},
            MNat.zero_ne_succ(List.length(&2, U32, t2))(al))
        case Con{+c, +ct2}:
          while_step_s(~p, h, t2, c, ct2, acc, p(c),
            while_s(~p, t2, ct2, Con{h, acc}, MNat.succ_inj(List.length(&2, B.Cl, ct2), List.length(&2, U32, t2), al)))

def while_step_a(~p: B.Cl -> Bool, +h: U32, +t: List<&2, U32>, +c: B.Cl, +ct: List<&2, B.Cl>, +acc: List<&2, U32>, b: Bool,
    al: {List.length(&2, B.Cl, Con{c, ct}) == List.length(&2, U32, Con{h, t}) : Nat},
    ih: {List.length(&2, B.Cl, B.rn.cs(B.run.while(~p, t, ct, Con{h, acc}))) == List.length(&2, U32, B.rn.xs(B.run.while(~p, t, ct, Con{h, acc}))) : Nat}) ->
    {List.length(&2, B.Cl, B.rn.cs(while_k(~p, h, t, c, ct, acc, b))) == List.length(&2, U32, B.rn.xs(while_k(~p, h, t, c, ct, acc, b))) : Nat}:
  match b:
    case True{}:
      ih
    case False{}:
      al

def while_a(~p: B.Cl -> Bool, t: List<&2, U32>, ct: List<&2, B.Cl>, +acc: List<&2, U32>, +al: {List.length(&2, B.Cl, ct) == List.length(&2, U32, t) : Nat}) ->
    {List.length(&2, B.Cl, B.rn.cs(B.run.while(~p, t, ct, acc))) == List.length(&2, U32, B.rn.xs(B.run.while(~p, t, ct, acc))) : Nat}:
  match t:
    case Nil{}:
      match ct:
        case Nil{}:
          {==}
        case Con{+c, +ct2}:
          Empty.absurd({List.length(&2, B.Cl, B.rn.cs(B.run.while(~p, Nil{}, Con{c, ct2}, acc))) == List.length(&2, U32, B.rn.xs(B.run.while(~p, Nil{}, Con{c, ct2}, acc))) : Nat},
            MNat.succ_ne_zero(List.length(&2, B.Cl, ct2))(al))
    case Con{+h, +t2}:
      match ct:
        case Nil{}:
          Empty.absurd({List.length(&2, B.Cl, B.rn.cs(B.run.while(~p, Con{h, t2}, Nil{}, acc))) == List.length(&2, U32, B.rn.xs(B.run.while(~p, Con{h, t2}, Nil{}, acc))) : Nat},
            MNat.zero_ne_succ(List.length(&2, U32, t2))(al))
        case Con{+c, +ct2}:
          while_step_a(~p, h, t2, c, ct2, acc, p(c), al,
            while_a(~p, t2, ct2, Con{h, acc}, MNat.succ_inj(List.length(&2, B.Cl, ct2), List.length(&2, U32, t2), al)))

def while_step_p(~p: B.Cl -> Bool, +h: U32, +t: List<&2, U32>, +c: B.Cl, +ct: List<&2, B.Cl>, +acc: List<&2, U32>, b: Bool,
    ih: MNat.le(List.length(&2, U32, B.rn.xs(B.run.while(~p, t, ct, Con{h, acc}))), List.length(&2, U32, t))) ->
    MNat.le(List.length(&2, U32, B.rn.xs(while_k(~p, h, t, c, ct, acc, b))), List.length(&2, U32, Con{h, t})):
  match b:
    case True{}:
      MNat.le_trans(List.length(&2, U32, B.rn.xs(B.run.while(~p, t, ct, Con{h, acc}))), List.length(&2, U32, t), List.length(&2, U32, Con{h, t}),
        ih, MNat.le_succ(List.length(&2, U32, t)))
    case False{}:
      MNat.le_refl(List.length(&2, U32, Con{h, t}))

def while_p(~p: B.Cl -> Bool, t: List<&2, U32>, ct: List<&2, B.Cl>, +acc: List<&2, U32>) ->
    MNat.le(List.length(&2, U32, B.rn.xs(B.run.while(~p, t, ct, acc))), List.length(&2, U32, t)):
  match t:
    case Nil{}:
      match ct:
        case Nil{}:
          MNat.le_refl(0n)
        case Con{c, ct2}:
          MNat.le_refl(0n)
    case Con{+h, +t2}:
      match ct:
        case Nil{}:
          MNat.zero_le(List.length(&2, U32, Con{h, t2}))
        case Con{+c, +ct2}:
          while_step_p(~p, h, t2, c, ct2, acc, p(c), while_p(~p, t2, ct2, Con{h, acc}))

# Quoted runs, to a closing quote

def quoted_k(~shut: B.Cl -> Bool, +h: U32, +t: List<&2, U32>, +c: B.Cl, +ct: List<&2, B.Cl>, +acc: List<&2, U32>, +esc: Bool, +b: Bool) -> B.Rn:
  B.when(B.Rn, b, u => B.Rn{Con{h, acc}, t, ct}, u => B.run.quoted(~shut, t, ct, Con{h, acc}, B.cl.back(c) && Bool.not(esc)))

def quoted_step_s(~shut: B.Cl -> Bool, +h: U32, +t: List<&2, U32>, +c: B.Cl, +ct: List<&2, B.Cl>, +acc: List<&2, U32>, +esc: Bool, b: Bool,
    ih: {List.append(&2, U32, List.reverse(&2, U32, Con{h, acc}), t) == spelt(B.run.quoted(~shut, t, ct, Con{h, acc}, B.cl.back(c) && Bool.not(esc))) : List<&2, U32>}) ->
    {List.append(&2, U32, List.reverse(&2, U32, acc), Con{h, t}) == spelt(quoted_k(~shut, h, t, c, ct, acc, esc, b)) : List<&2, U32>}:
  match b:
    case True{}:
      took(acc, h, t)
    case False{}:
      Equal.trans(List<&2, U32>, List.append(&2, U32, List.reverse(&2, U32, acc), Con{h, t}), List.append(&2, U32, List.reverse(&2, U32, Con{h, acc}), t),
        spelt(B.run.quoted(~shut, t, ct, Con{h, acc}, B.cl.back(c) && Bool.not(esc))), took(acc, h, t), ih)

def quoted_s(~shut: B.Cl -> Bool, t: List<&2, U32>, ct: List<&2, B.Cl>, +acc: List<&2, U32>, +esc: Bool, +al: {List.length(&2, B.Cl, ct) == List.length(&2, U32, t) : Nat}) ->
    {List.append(&2, U32, List.reverse(&2, U32, acc), t) == spelt(B.run.quoted(~shut, t, ct, acc, esc)) : List<&2, U32>}:
  match t:
    case Nil{}:
      match ct:
        case Nil{}:
          {==}
        case Con{+c, +ct2}:
          Empty.absurd({List.append(&2, U32, List.reverse(&2, U32, acc), Nil{}) == spelt(B.run.quoted(~shut, Nil{}, Con{c, ct2}, acc, esc)) : List<&2, U32>},
            MNat.succ_ne_zero(List.length(&2, B.Cl, ct2))(al))
    case Con{+h, +t2}:
      match ct:
        case Nil{}:
          Empty.absurd({List.append(&2, U32, List.reverse(&2, U32, acc), Con{h, t2}) == spelt(B.run.quoted(~shut, Con{h, t2}, Nil{}, acc, esc)) : List<&2, U32>},
            MNat.zero_ne_succ(List.length(&2, U32, t2))(al))
        case Con{+c, +ct2}:
          quoted_step_s(~shut, h, t2, c, ct2, acc, esc, shut(c) && Bool.not(esc),
            quoted_s(~shut, t2, ct2, Con{h, acc}, B.cl.back(c) && Bool.not(esc), MNat.succ_inj(List.length(&2, B.Cl, ct2), List.length(&2, U32, t2), al)))

def quoted_step_a(~shut: B.Cl -> Bool, +h: U32, +t: List<&2, U32>, +c: B.Cl, +ct: List<&2, B.Cl>, +acc: List<&2, U32>, +esc: Bool, b: Bool,
    al: {List.length(&2, B.Cl, ct) == List.length(&2, U32, t) : Nat},
    ih: {List.length(&2, B.Cl, B.rn.cs(B.run.quoted(~shut, t, ct, Con{h, acc}, B.cl.back(c) && Bool.not(esc)))) ==
      List.length(&2, U32, B.rn.xs(B.run.quoted(~shut, t, ct, Con{h, acc}, B.cl.back(c) && Bool.not(esc)))) : Nat}) ->
    {List.length(&2, B.Cl, B.rn.cs(quoted_k(~shut, h, t, c, ct, acc, esc, b))) == List.length(&2, U32, B.rn.xs(quoted_k(~shut, h, t, c, ct, acc, esc, b))) : Nat}:
  match b:
    case True{}:
      al
    case False{}:
      ih

def quoted_a(~shut: B.Cl -> Bool, t: List<&2, U32>, ct: List<&2, B.Cl>, +acc: List<&2, U32>, +esc: Bool, +al: {List.length(&2, B.Cl, ct) == List.length(&2, U32, t) : Nat}) ->
    {List.length(&2, B.Cl, B.rn.cs(B.run.quoted(~shut, t, ct, acc, esc))) == List.length(&2, U32, B.rn.xs(B.run.quoted(~shut, t, ct, acc, esc))) : Nat}:
  match t:
    case Nil{}:
      match ct:
        case Nil{}:
          {==}
        case Con{+c, +ct2}:
          Empty.absurd({List.length(&2, B.Cl, B.rn.cs(B.run.quoted(~shut, Nil{}, Con{c, ct2}, acc, esc))) == List.length(&2, U32, B.rn.xs(B.run.quoted(~shut, Nil{}, Con{c, ct2}, acc, esc))) : Nat},
            MNat.succ_ne_zero(List.length(&2, B.Cl, ct2))(al))
    case Con{+h, +t2}:
      match ct:
        case Nil{}:
          Empty.absurd({List.length(&2, B.Cl, B.rn.cs(B.run.quoted(~shut, Con{h, t2}, Nil{}, acc, esc))) == List.length(&2, U32, B.rn.xs(B.run.quoted(~shut, Con{h, t2}, Nil{}, acc, esc))) : Nat},
            MNat.zero_ne_succ(List.length(&2, U32, t2))(al))
        case Con{+c, +ct2}:
          quoted_step_a(~shut, h, t2, c, ct2, acc, esc, shut(c) && Bool.not(esc), MNat.succ_inj(List.length(&2, B.Cl, ct2), List.length(&2, U32, t2), al),
            quoted_a(~shut, t2, ct2, Con{h, acc}, B.cl.back(c) && Bool.not(esc), MNat.succ_inj(List.length(&2, B.Cl, ct2), List.length(&2, U32, t2), al)))

def quoted_step_p(~shut: B.Cl -> Bool, +h: U32, +t: List<&2, U32>, +c: B.Cl, +ct: List<&2, B.Cl>, +acc: List<&2, U32>, +esc: Bool, b: Bool,
    ih: MNat.le(List.length(&2, U32, B.rn.xs(B.run.quoted(~shut, t, ct, Con{h, acc}, B.cl.back(c) && Bool.not(esc)))), List.length(&2, U32, t))) ->
    MNat.le(List.length(&2, U32, B.rn.xs(quoted_k(~shut, h, t, c, ct, acc, esc, b))), List.length(&2, U32, Con{h, t})):
  match b:
    case True{}:
      MNat.le_succ(List.length(&2, U32, t))
    case False{}:
      MNat.le_trans(List.length(&2, U32, B.rn.xs(B.run.quoted(~shut, t, ct, Con{h, acc}, B.cl.back(c) && Bool.not(esc)))), List.length(&2, U32, t), List.length(&2, U32, Con{h, t}),
        ih, MNat.le_succ(List.length(&2, U32, t)))

def quoted_p(~shut: B.Cl -> Bool, t: List<&2, U32>, ct: List<&2, B.Cl>, +acc: List<&2, U32>, +esc: Bool) ->
    MNat.le(List.length(&2, U32, B.rn.xs(B.run.quoted(~shut, t, ct, acc, esc))), List.length(&2, U32, t)):
  match t:
    case Nil{}:
      match ct:
        case Nil{}:
          MNat.le_refl(0n)
        case Con{c, ct2}:
          MNat.le_refl(0n)
    case Con{+h, +t2}:
      match ct:
        case Nil{}:
          MNat.zero_le(List.length(&2, U32, Con{h, t2}))
        case Con{+c, +ct2}:
          quoted_step_p(~shut, h, t2, c, ct2, acc, esc, shut(c) && Bool.not(esc), quoted_p(~shut, t2, ct2, Con{h, acc}, B.cl.back(c) && Bool.not(esc)))

# The tokens

# a symbol's token, a byte alone
def sym_step(+out: List<&2, B.Tok>, +h: U32, +t: List<&2, U32>, +k: Nat, +ct: List<&2, B.Cl>,
    ih: {List.append(&2, U32, B.toks.text(List.reverse(&2, B.Tok, Con{B.TSym{h}, out})), t) == B.toks.text(B.toks.go(k, t, ct, Con{B.TSym{h}, out})) : List<&2, U32>}) ->
    {List.append(&2, U32, B.toks.text(List.reverse(&2, B.Tok, out)), Con{h, t}) == B.toks.text(B.toks.go(k, t, ct, Con{B.TSym{h}, out})) : List<&2, U32>}:
  %ih : {List.append(&2, U32, B.toks.text(List.reverse(&2, B.Tok, out)), Con{h, t}) == _ : List<&2, U32>}
  %text_snoc(out, B.TSym{h}) : {List.append(&2, U32, B.toks.text(List.reverse(&2, B.Tok, out)), Con{h, t}) == List.append(&2, U32, _, t) : List<&2, U32>}
  %assoc_r(B.toks.text(List.reverse(&2, B.Tok, out)), [h], t) : {List.append(&2, U32, B.toks.text(List.reverse(&2, B.Tok, out)), Con{h, t}) == _ : List<&2, U32>}
  {==}

# a run's token, mk making it of the bytes the run took: those bytes
# spelt by the run (s), the rest by the hypothesis
def run_step(~mk: List<&2, U32> -> B.Tok, +out: List<&2, B.Tok>, +h: U32, +t: List<&2, U32>, +k: Nat, +r: B.Rn,
    +s: {Con{h, t} == spelt(r) : List<&2, U32>},
    mb: {B.tok.bytes(mk(List.reverse(&2, U32, B.rn.acc(r)))) == List.reverse(&2, U32, B.rn.acc(r)) : List<&2, U32>},
    ih: {List.append(&2, U32, B.toks.text(List.reverse(&2, B.Tok, Con{mk(List.reverse(&2, U32, B.rn.acc(r))), out})), B.rn.xs(r)) ==
      B.toks.text(B.toks.go(k, B.rn.xs(r), B.rn.cs(r), Con{mk(List.reverse(&2, U32, B.rn.acc(r))), out})) : List<&2, U32>}) ->
    {List.append(&2, U32, B.toks.text(List.reverse(&2, B.Tok, out)), Con{h, t}) ==
      B.toks.text(B.toks.go(k, B.rn.xs(r), B.rn.cs(r), Con{mk(List.reverse(&2, U32, B.rn.acc(r))), out})) : List<&2, U32>}:
  %ih : {List.append(&2, U32, B.toks.text(List.reverse(&2, B.Tok, out)), Con{h, t}) == _ : List<&2, U32>}
  %text_snoc(out, mk(List.reverse(&2, U32, B.rn.acc(r)))) :
    {List.append(&2, U32, B.toks.text(List.reverse(&2, B.Tok, out)), Con{h, t}) == List.append(&2, U32, _, B.rn.xs(r)) : List<&2, U32>}
  %Equal.sym(List<&2, U32>, B.tok.bytes(mk(List.reverse(&2, U32, B.rn.acc(r)))), List.reverse(&2, U32, B.rn.acc(r)), mb) :
    {List.append(&2, U32, B.toks.text(List.reverse(&2, B.Tok, out)), Con{h, t}) ==
      List.append(&2, U32, List.append(&2, U32, B.toks.text(List.reverse(&2, B.Tok, out)), _), B.rn.xs(r)) : List<&2, U32>}
  %assoc_r(B.toks.text(List.reverse(&2, B.Tok, out)), List.reverse(&2, U32, B.rn.acc(r)), B.rn.xs(r)) :
    {List.append(&2, U32, B.toks.text(List.reverse(&2, B.Tok, out)), Con{h, t}) == _ : List<&2, U32>}
  %s : {List.append(&2, U32, B.toks.text(List.reverse(&2, B.Tok, out)), Con{h, t}) == List.append(&2, U32, B.toks.text(List.reverse(&2, B.Tok, out)), _) : List<&2, U32>}
  {==}

# what the tokens so far spell, then what is left, is what the tokens
# returned spell, given fuel for each byte left and classes in step
def toks_spell(n: Nat, xs: List<&2, U32>, cs: List<&2, B.Cl>, +out: List<&2, B.Tok>,
    +al: {List.length(&2, B.Cl, cs) == List.length(&2, U32, xs) : Nat}, +f: MNat.le(List.length(&2, U32, xs), n)) ->
    {List.append(&2, U32, B.toks.text(List.reverse(&2, B.Tok, out)), xs) == B.toks.text(B.toks.go(n, xs, cs, out)) : List<&2, U32>}:
  match n:
    case 0n:
      match xs:
        case Nil{}:
          ML.append_nil(&2, U32, B.toks.text(List.reverse(&2, B.Tok, out)))
        case Con{+h, +t}:
          Empty.absurd({List.append(&2, U32, B.toks.text(List.reverse(&2, B.Tok, out)), Con{h, t}) == B.toks.text(B.toks.go(0n, Con{h, t}, cs, out)) : List<&2, U32>},
            MB.false_ne_true()(f))
    case 1n+(+k):
      match xs:
        case Nil{}:
          match cs:
            case Nil{}:
              ML.append_nil(&2, U32, B.toks.text(List.reverse(&2, B.Tok, out)))
            case Con{c, ct}:
              ML.append_nil(&2, U32, B.toks.text(List.reverse(&2, B.Tok, out)))
        case Con{+h, +t}:
          match cs:
            case Nil{}:
              Empty.absurd({List.append(&2, U32, B.toks.text(List.reverse(&2, B.Tok, out)), Con{h, t}) == B.toks.text(B.toks.go(1n+k, Con{h, t}, Nil{}, out)) : List<&2, U32>},
                MNat.zero_ne_succ(List.length(&2, U32, t))(al))
            case Con{c, +ct}:
              match c:
                case B.CSp{}:
                  +al1 = MNat.succ_inj(List.length(&2, B.Cl, ct), List.length(&2, U32, t), al)
                  +f1 = MNat.le_of_succ_le_succ(List.length(&2, U32, t), k, f)
                  run_step(~(x => B.TSp{x}), out, h, t, k, B.run.while(~B.cl.sp, t, ct, [h]), while_s(~B.cl.sp, t, ct, [h], al1), {==},
                    toks_spell(k, B.rn.xs(B.run.while(~B.cl.sp, t, ct, [h])), B.rn.cs(B.run.while(~B.cl.sp, t, ct, [h])), Con{B.TSp{List.reverse(&2, U32, B.rn.acc(B.run.while(~B.cl.sp, t, ct, [h])))}, out},
                      while_a(~B.cl.sp, t, ct, [h], al1),
                      MNat.le_trans(List.length(&2, U32, B.rn.xs(B.run.while(~B.cl.sp, t, ct, [h]))), List.length(&2, U32, t), k, while_p(~B.cl.sp, t, ct, [h]), f1)))
                case B.CAlpha{}:
                  +al1 = MNat.succ_inj(List.length(&2, B.Cl, ct), List.length(&2, U32, t), al)
                  +f1 = MNat.le_of_succ_le_succ(List.length(&2, U32, t), k, f)
                  run_step(~(x => B.TName{x}), out, h, t, k, B.run.while(~B.cl.name, t, ct, [h]), while_s(~B.cl.name, t, ct, [h], al1), {==},
                    toks_spell(k, B.rn.xs(B.run.while(~B.cl.name, t, ct, [h])), B.rn.cs(B.run.while(~B.cl.name, t, ct, [h])), Con{B.TName{List.reverse(&2, U32, B.rn.acc(B.run.while(~B.cl.name, t, ct, [h])))}, out},
                      while_a(~B.cl.name, t, ct, [h], al1),
                      MNat.le_trans(List.length(&2, U32, B.rn.xs(B.run.while(~B.cl.name, t, ct, [h]))), List.length(&2, U32, t), k, while_p(~B.cl.name, t, ct, [h]), f1)))
                case B.CDigit{}:
                  +al1 = MNat.succ_inj(List.length(&2, B.Cl, ct), List.length(&2, U32, t), al)
                  +f1 = MNat.le_of_succ_le_succ(List.length(&2, U32, t), k, f)
                  run_step(~(x => B.TNum{x}), out, h, t, k, B.run.while(~B.cl.alnum, t, ct, [h]), while_s(~B.cl.alnum, t, ct, [h], al1), {==},
                    toks_spell(k, B.rn.xs(B.run.while(~B.cl.alnum, t, ct, [h])), B.rn.cs(B.run.while(~B.cl.alnum, t, ct, [h])), Con{B.TNum{List.reverse(&2, U32, B.rn.acc(B.run.while(~B.cl.alnum, t, ct, [h])))}, out},
                      while_a(~B.cl.alnum, t, ct, [h], al1),
                      MNat.le_trans(List.length(&2, U32, B.rn.xs(B.run.while(~B.cl.alnum, t, ct, [h]))), List.length(&2, U32, t), k, while_p(~B.cl.alnum, t, ct, [h]), f1)))
                case B.CQuote{}:
                  +al1 = MNat.succ_inj(List.length(&2, B.Cl, ct), List.length(&2, U32, t), al)
                  +f1 = MNat.le_of_succ_le_succ(List.length(&2, U32, t), k, f)
                  run_step(~(x => B.TStr{x}), out, h, t, k, B.run.quoted(~B.cl.quote, t, ct, [h], False{}), quoted_s(~B.cl.quote, t, ct, [h], False{}, al1), {==},
                    toks_spell(k, B.rn.xs(B.run.quoted(~B.cl.quote, t, ct, [h], False{})), B.rn.cs(B.run.quoted(~B.cl.quote, t, ct, [h], False{})), Con{B.TStr{List.reverse(&2, U32, B.rn.acc(B.run.quoted(~B.cl.quote, t, ct, [h], False{})))}, out},
                      quoted_a(~B.cl.quote, t, ct, [h], False{}, al1),
                      MNat.le_trans(List.length(&2, U32, B.rn.xs(B.run.quoted(~B.cl.quote, t, ct, [h], False{}))), List.length(&2, U32, t), k, quoted_p(~B.cl.quote, t, ct, [h], False{}), f1)))
                case B.CHash{}:
                  text_snoc(out, B.TCom{Con{h, t}})
                case B.CCaret{}:
                  +al1 = MNat.succ_inj(List.length(&2, B.Cl, ct), List.length(&2, U32, t), al)
                  +f1 = MNat.le_of_succ_le_succ(List.length(&2, U32, t), k, f)
                  run_step(~(x => B.TName{x}), out, h, t, k, B.run.host(B.run.while(~B.cl.caret, t, ct, [h])),
                    Equal.trans(List<&2, U32>, Con{h, t}, spelt(B.run.while(~B.cl.caret, t, ct, [h])), spelt(B.run.host(B.run.while(~B.cl.caret, t, ct, [h]))), while_s(~B.cl.caret, t, ct, [h], al1),
                      while_s(~B.cl.name, B.rn.xs(B.run.while(~B.cl.caret, t, ct, [h])), B.rn.cs(B.run.while(~B.cl.caret, t, ct, [h])), B.rn.acc(B.run.while(~B.cl.caret, t, ct, [h])), while_a(~B.cl.caret, t, ct, [h], al1))), {==},
                    toks_spell(k, B.rn.xs(B.run.host(B.run.while(~B.cl.caret, t, ct, [h]))), B.rn.cs(B.run.host(B.run.while(~B.cl.caret, t, ct, [h]))), Con{B.TName{List.reverse(&2, U32, B.rn.acc(B.run.host(B.run.while(~B.cl.caret, t, ct, [h]))))}, out},
                      while_a(~B.cl.name, B.rn.xs(B.run.while(~B.cl.caret, t, ct, [h])), B.rn.cs(B.run.while(~B.cl.caret, t, ct, [h])), B.rn.acc(B.run.while(~B.cl.caret, t, ct, [h])), while_a(~B.cl.caret, t, ct, [h], al1)),
                      MNat.le_trans(List.length(&2, U32, B.rn.xs(B.run.host(B.run.while(~B.cl.caret, t, ct, [h])))), List.length(&2, U32, B.rn.xs(B.run.while(~B.cl.caret, t, ct, [h]))), k,
                        while_p(~B.cl.name, B.rn.xs(B.run.while(~B.cl.caret, t, ct, [h])), B.rn.cs(B.run.while(~B.cl.caret, t, ct, [h])), B.rn.acc(B.run.while(~B.cl.caret, t, ct, [h]))),
                        MNat.le_trans(List.length(&2, U32, B.rn.xs(B.run.while(~B.cl.caret, t, ct, [h]))), List.length(&2, U32, t), k, while_p(~B.cl.caret, t, ct, [h]), f1))))
                case B.CTilde{}:
                  +al1 = MNat.succ_inj(List.length(&2, B.Cl, ct), List.length(&2, U32, t), al)
                  +f1 = MNat.le_of_succ_le_succ(List.length(&2, U32, t), k, f)
                  run_step(~(x => B.TName{x}), out, h, t, k, B.run.while(~B.cl.name, t, ct, [h]), while_s(~B.cl.name, t, ct, [h], al1), {==},
                    toks_spell(k, B.rn.xs(B.run.while(~B.cl.name, t, ct, [h])), B.rn.cs(B.run.while(~B.cl.name, t, ct, [h])), Con{B.TName{List.reverse(&2, U32, B.rn.acc(B.run.while(~B.cl.name, t, ct, [h])))}, out},
                      while_a(~B.cl.name, t, ct, [h], al1),
                      MNat.le_trans(List.length(&2, U32, B.rn.xs(B.run.while(~B.cl.name, t, ct, [h]))), List.length(&2, U32, t), k, while_p(~B.cl.name, t, ct, [h]), f1)))
                case B.CTick{}:
                  +al1 = MNat.succ_inj(List.length(&2, B.Cl, ct), List.length(&2, U32, t), al)
                  +f1 = MNat.le_of_succ_le_succ(List.length(&2, U32, t), k, f)
                  run_step(~(x => B.TStr{x}), out, h, t, k, B.run.quoted(~B.cl.tick, t, ct, [h], False{}), quoted_s(~B.cl.tick, t, ct, [h], False{}, al1), {==},
                    toks_spell(k, B.rn.xs(B.run.quoted(~B.cl.tick, t, ct, [h], False{})), B.rn.cs(B.run.quoted(~B.cl.tick, t, ct, [h], False{})), Con{B.TStr{List.reverse(&2, U32, B.rn.acc(B.run.quoted(~B.cl.tick, t, ct, [h], False{})))}, out},
                      quoted_a(~B.cl.tick, t, ct, [h], False{}, al1),
                      MNat.le_trans(List.length(&2, U32, B.rn.xs(B.run.quoted(~B.cl.tick, t, ct, [h], False{}))), List.length(&2, U32, t), k, quoted_p(~B.cl.tick, t, ct, [h], False{}), f1)))
                case B.CDot{}:
                  +al1 = MNat.succ_inj(List.length(&2, B.Cl, ct), List.length(&2, U32, t), al)
                  +f1 = MNat.le_of_succ_le_succ(List.length(&2, U32, t), k, f)
                  sym_step(out, h, t, k, ct, toks_spell(k, t, ct, Con{B.TSym{h}, out}, al1, f1))
                case B.CBack{}:
                  +al1 = MNat.succ_inj(List.length(&2, B.Cl, ct), List.length(&2, U32, t), al)
                  +f1 = MNat.le_of_succ_le_succ(List.length(&2, U32, t), k, f)
                  sym_step(out, h, t, k, ct, toks_spell(k, t, ct, Con{B.TSym{h}, out}, al1, f1))
                case B.COther{}:
                  +al1 = MNat.succ_inj(List.length(&2, B.Cl, ct), List.length(&2, U32, t), al)
                  +f1 = MNat.le_of_succ_le_succ(List.length(&2, U32, t), k, f)
                  sym_step(out, h, t, k, ct, toks_spell(k, t, ct, Con{B.TSym{h}, out}, al1, f1))

def Laws.tokens.spell(xs):
  Equal.sym(List<&2, U32>, xs, B.toks.text(B.toks(xs)),
    toks_spell(List.length(&2, U32, xs), xs, B.classes(xs), Nil{}, len_classes(xs), MNat.le_refl(List.length(&2, U32, xs))))

# Lines
# -----
#
# lines.go keeps the line so far reversed in cur and the lines done
# reversed in out: the lines done, each with its newline (jl), then the
# line so far, then what is left less its carriage returns, are what the
# lines it returns join to. A line's indentation is counted in a Nat and
# kept in a U32, exact for a file shorter than 2^32 bytes (lim).

def lim_left(+a: Nat, +b: Nat, +N: Nat, h: MNat.lt(Nat.add(a, b), N)) -> MNat.lt(a, N):
  MNat.lt_of_le_of_lt(a, Nat.add(a, b), N, MNat.le_add_right(a, b), h)

def lim_right(+a: Nat, +b: Nat, +N: Nat, h: MNat.lt(Nat.add(a, b), N)) -> MNat.lt(b, N):
  MNat.lt_of_le_of_lt(b, Nat.add(a, b), N,
    ME.subst(Nat, x => MNat.le(b, x), Nat.add(b, a), Nat.add(a, b), MNat.add_comm(b, a), MNat.le_add_right(b, a)), h)

def lim_succ(+a: Nat, +m: Nat, +N: Nat, h: MNat.lt(Nat.add(a, 1n+m), N)) -> MNat.lt(1n+Nat.add(a, m), N):
  ME.subst(Nat, x => MNat.lt(x, N), Nat.add(a, 1n+m), 1n+Nat.add(a, m), MNat.add_succ(a, m), h)

def lim_pred(+x: Nat, +N: Nat, h: MNat.lt(1n+x, N)) -> MNat.lt(x, N):
  MNat.lt_of_le_of_lt(x, 1n+x, N, MNat.le_succ(x), h)

def lim_zero(+a: Nat, +N: Nat, h: MNat.lt(Nat.add(a, 0n), N)) -> MNat.lt(a, N):
  ME.subst(Nat, x => MNat.lt(x, N), Nat.add(a, 0n), a, MNat.add_zero(a), h)

def lim_rev(+cur: List<&2, U32>, +N: Nat, h: MNat.lt(List.length(&2, U32, cur), N)) -> MNat.lt(List.length(&2, U32, List.reverse(&2, U32, cur)), N):
  ME.subst(Nat, x => MNat.lt(x, N), List.length(&2, U32, cur), List.length(&2, U32, List.reverse(&2, U32, cur)),
    Equal.sym(Nat, List.length(&2, U32, List.reverse(&2, U32, cur)), List.length(&2, U32, cur), ML.length_reverse(&2, U32, cur)), h)

# a bound abstract, known to be 2^32: a concrete bound behind a successor
# makes Bend unfold 2^32 when it compares, overflowing its stack
def to32(+n: Nat, +N: Nat, +hN: {N == Nat.pow(2n, 32n) : Nat}, h: MNat.lt(n, N)) -> MNat.lt(n, Nat.pow(2n, 32n)):
  ME.subst(Nat, M => MNat.lt(n, M), N, Nat.pow(2n, 32n), hN, h)

# a space after spaces
def sp_snoc(n: Nat, +t: List<&2, U32>) ->
    {List.append(&2, U32, List.replicate(U32, n, 32), Con{32, t}) == Con{32, List.append(&2, U32, List.replicate(U32, n, 32), t)} : List<&2, U32>}:
  match n:
    case 0n:
      {==}
    case 1n+k:
      %sp_snoc(k, t) : {Con{32, List.append(&2, U32, List.replicate(U32, k, 32), Con{32, t})} == Con{32, _} : List<&2, U32>}
      {==}

def line_step(+c: U32, +t: List<&2, U32>, +n: Nat, +no: U32, +N: Nat, +hN: {N == Nat.pow(2n, 32n) : Nat}, b: Bool, +e: {b == U32.is_eq(c, 32) : Bool},
    +h: MNat.lt(Nat.add(n, 1n+List.length(&2, U32, t)), N),
    ih: {List.append(&2, U32, List.replicate(U32, 1n+n, 32), t) == B.ln.text(B.line.of(t, 1n+n, no)) : List<&2, U32>}) ->
    {List.append(&2, U32, List.replicate(U32, n, 32), Con{c, t}) ==
      B.ln.text(B.when(B.Ln, b, u => B.line.of(t, 1n+n, no), u => B.Ln{no, U32.from_nat(n), Con{c, t}})) : List<&2, U32>}:
  match b:
    case True{}:
      %Equal.sym(U32, c, 32, u32_eq_of_is_eq(c, 32, Equal.sym(Bool, True{}, U32.is_eq(c, 32), e))) :
        {List.append(&2, U32, List.replicate(U32, n, 32), Con{_, t}) == B.ln.text(B.line.of(t, 1n+n, no)) : List<&2, U32>}
      %ih : {List.append(&2, U32, List.replicate(U32, n, 32), Con{32, t}) == _ : List<&2, U32>}
      sp_snoc(n, t)
    case False{}:
      %MU.u32_to_nat_from_nat_sym(n, to32(n, N, hN, lim_left(n, 1n+List.length(&2, U32, t), N, h))) :
        {List.append(&2, U32, List.replicate(U32, n, 32), Con{c, t}) == List.append(&2, U32, List.replicate(U32, _, 32), Con{c, t}) : List<&2, U32>}
      {==}

# a line read: its spaces counted, then its text, are its bytes
def line_text(xs: List<&2, U32>, +n: Nat, +no: U32, +N: Nat, +hN: {N == Nat.pow(2n, 32n) : Nat}, +h: MNat.lt(Nat.add(n, List.length(&2, U32, xs)), N)) ->
    {List.append(&2, U32, List.replicate(U32, n, 32), xs) == B.ln.text(B.line.of(xs, n, no)) : List<&2, U32>}:
  match xs:
    case Nil{}:
      %MU.u32_to_nat_from_nat_sym(n, to32(n, N, hN, lim_zero(n, N, h))) :
        {List.append(&2, U32, List.replicate(U32, n, 32), Nil{}) == List.append(&2, U32, List.replicate(U32, _, 32), Nil{}) : List<&2, U32>}
      {==}
    case Con{+c, +t}:
      line_step(c, t, n, no, N, hN, U32.is_eq(c, 32), {==}, h, line_text(t, 1n+n, no, N, hN, lim_succ(n, List.length(&2, U32, t), N, h)))

# lines in order, each followed by its newline
def jl(ls: List<&2, B.Ln>) -> List<&2, U32>:
  match ls:
    case Nil{}:
      Nil{}
    case Con{l, r}:
      List.append(&2, U32, B.ln.text(l), Con{10, jl(r)})

def revsl_snoc(+xs: List<&2, B.Ln>, +y: B.Ln) ->
    {List.append(&2, B.Ln, List.reverse(&2, B.Ln, xs), [y]) == List.reverse.go(&2, B.Ln, xs, [y]) : List<&2, B.Ln>}:
  Equal.sym(List<&2, B.Ln>, List.reverse.go(&2, B.Ln, xs, [y]), List.append(&2, B.Ln, List.reverse(&2, B.Ln, xs), [y]),
    ML.reverse_go_spec(&2, B.Ln, xs, [y]))

def jl_snoc(ls: List<&2, B.Ln>, +x: B.Ln) ->
    {List.append(&2, U32, jl(ls), List.append(&2, U32, B.ln.text(x), [10])) == jl(List.append(&2, B.Ln, ls, [x])) : List<&2, U32>}:
  match ls:
    case Nil{}:
      {==}
    case Con{+p, +r}:
      %jl_snoc(r, x) : {List.append(&2, U32, List.append(&2, U32, B.ln.text(p), Con{10, jl(r)}), List.append(&2, U32, B.ln.text(x), [10])) ==
        List.append(&2, U32, B.ln.text(p), Con{10, _}) : List<&2, U32>}
      ML.append_assoc(&2, U32, B.ln.text(p), Con{10, jl(r)}, List.append(&2, U32, B.ln.text(x), [10]))

def text_lsnoc(ls: List<&2, B.Ln>, +x: B.Ln) ->
    {List.append(&2, U32, jl(ls), B.ln.text(x)) == B.lines.text(List.append(&2, B.Ln, ls, [x])) : List<&2, U32>}:
  match ls:
    case Nil{}:
      {==}
    case Con{+p, r}:
      match r:
        case Nil{}:
          ML.append_assoc(&2, U32, B.ln.text(p), [10], B.ln.text(x))
        case Con{+q, +r2}:
          %text_lsnoc(Con{q, r2}, x) : {List.append(&2, U32, List.append(&2, U32, B.ln.text(p), Con{10, jl(Con{q, r2})}), B.ln.text(x)) ==
            List.append(&2, U32, B.ln.text(p), Con{10, _}) : List<&2, U32>}
          ML.append_assoc(&2, U32, B.ln.text(p), Con{10, jl(Con{q, r2})}, B.ln.text(x))

def uncr_k(+b: U32, +t: List<&2, U32>, +b2: Bool) -> List<&2, U32>:
  B.when(List<&2, U32>, b2, u => B.uncr(t), u => Con{b, B.uncr(t)})

def lines_k(+b: U32, +t: List<&2, U32>, +cur: List<&2, U32>, +no: U32, +out: List<&2, B.Ln>, +b1: Bool, +b2: Bool) -> List<&2, B.Ln>:
  B.when(List<&2, B.Ln>, b1, u => B.lines.go(t, Nil{}, (no + 1 : U32), Con{B.lines.line(cur, no), out}),
    u => B.when(List<&2, B.Ln>, b2, v => B.lines.go(t, cur, no, out), v => B.lines.go(t, Con{b, cur}, no, out)))

# the last line
def lines_end(+cur: List<&2, U32>, +no: U32, +out: List<&2, B.Ln>, +N: Nat, +hN: {N == Nat.pow(2n, 32n) : Nat}, +hl: MNat.lt(List.length(&2, U32, List.reverse(&2, U32, cur)), N)) ->
    {List.append(&2, U32, jl(List.reverse(&2, B.Ln, out)), List.append(&2, U32, List.reverse(&2, U32, cur), Nil{})) ==
      B.lines.text(B.lines.go(Nil{}, cur, no, out)) : List<&2, U32>}:
  %revsl_snoc(out, B.lines.line(cur, no)) :
    {List.append(&2, U32, jl(List.reverse(&2, B.Ln, out)), List.append(&2, U32, List.reverse(&2, U32, cur), Nil{})) == B.lines.text(_) : List<&2, U32>}
  %text_lsnoc(List.reverse(&2, B.Ln, out), B.lines.line(cur, no)) :
    {List.append(&2, U32, jl(List.reverse(&2, B.Ln, out)), List.append(&2, U32, List.reverse(&2, U32, cur), Nil{})) == _ : List<&2, U32>}
  %line_text(List.reverse(&2, U32, cur), 0n, no, N, hN, hl) :
    {List.append(&2, U32, jl(List.reverse(&2, B.Ln, out)), List.append(&2, U32, List.reverse(&2, U32, cur), Nil{})) == List.append(&2, U32, jl(List.reverse(&2, B.Ln, out)), _) : List<&2, U32>}
  %ML.append_nil(&2, U32, List.reverse(&2, U32, cur)) :
    {List.append(&2, U32, jl(List.reverse(&2, B.Ln, out)), List.append(&2, U32, List.reverse(&2, U32, cur), Nil{})) == List.append(&2, U32, jl(List.reverse(&2, B.Ln, out)), _) : List<&2, U32>}
  {==}

# a byte after the line so far: a newline, a carriage return, or another
def lines_step(+b: U32, +t: List<&2, U32>, +cur: List<&2, U32>, +no: U32, +out: List<&2, B.Ln>, +N: Nat, +hN: {N == Nat.pow(2n, 32n) : Nat},
    b1: Bool, +e1: {b1 == U32.is_eq(b, 10) : Bool}, b2: Bool, +e2: {b2 == U32.is_eq(b, 13) : Bool},
    +hl: MNat.lt(List.length(&2, U32, List.reverse(&2, U32, cur)), N),
    ih_nl: {List.append(&2, U32, jl(List.reverse(&2, B.Ln, Con{B.lines.line(cur, no), out})), List.append(&2, U32, List.reverse(&2, U32, Nil{}), B.uncr(t))) ==
      B.lines.text(B.lines.go(t, Nil{}, (no + 1 : U32), Con{B.lines.line(cur, no), out})) : List<&2, U32>},
    ih_cr: {List.append(&2, U32, jl(List.reverse(&2, B.Ln, out)), List.append(&2, U32, List.reverse(&2, U32, cur), B.uncr(t))) ==
      B.lines.text(B.lines.go(t, cur, no, out)) : List<&2, U32>},
    ih_ch: {List.append(&2, U32, jl(List.reverse(&2, B.Ln, out)), List.append(&2, U32, List.reverse(&2, U32, Con{b, cur}), B.uncr(t))) ==
      B.lines.text(B.lines.go(t, Con{b, cur}, no, out)) : List<&2, U32>}) ->
    {List.append(&2, U32, jl(List.reverse(&2, B.Ln, out)), List.append(&2, U32, List.reverse(&2, U32, cur), uncr_k(b, t, b2))) ==
      B.lines.text(lines_k(b, t, cur, no, out, b1, b2)) : List<&2, U32>}:
  match b1:
    case True{}:
      match b2:
        case True{}:
          Empty.absurd({List.append(&2, U32, jl(List.reverse(&2, B.Ln, out)), List.append(&2, U32, List.reverse(&2, U32, cur), uncr_k(b, t, True{}))) ==
              B.lines.text(lines_k(b, t, cur, no, out, True{}, True{})) : List<&2, U32>},
            MB.true_ne_false()(ME.subst(U32, x => {True{} == U32.is_eq(x, 13) : Bool}, b, 10,
              u32_eq_of_is_eq(b, 10, Equal.sym(Bool, True{}, U32.is_eq(b, 10), e1)), e2)))
        case False{}:
          %Equal.sym(U32, b, 10, u32_eq_of_is_eq(b, 10, Equal.sym(Bool, True{}, U32.is_eq(b, 10), e1))) :
            {List.append(&2, U32, jl(List.reverse(&2, B.Ln, out)), List.append(&2, U32, List.reverse(&2, U32, cur), Con{_, B.uncr(t)})) ==
              B.lines.text(B.lines.go(t, Nil{}, (no + 1 : U32), Con{B.lines.line(cur, no), out})) : List<&2, U32>}
          %ih_nl : {List.append(&2, U32, jl(List.reverse(&2, B.Ln, out)), List.append(&2, U32, List.reverse(&2, U32, cur), Con{10, B.uncr(t)})) == _ : List<&2, U32>}
          %revsl_snoc(out, B.lines.line(cur, no)) :
            {List.append(&2, U32, jl(List.reverse(&2, B.Ln, out)), List.append(&2, U32, List.reverse(&2, U32, cur), Con{10, B.uncr(t)})) == List.append(&2, U32, jl(_), B.uncr(t)) : List<&2, U32>}
          %jl_snoc(List.reverse(&2, B.Ln, out), B.lines.line(cur, no)) :
            {List.append(&2, U32, jl(List.reverse(&2, B.Ln, out)), List.append(&2, U32, List.reverse(&2, U32, cur), Con{10, B.uncr(t)})) == List.append(&2, U32, _, B.uncr(t)) : List<&2, U32>}
          %line_text(List.reverse(&2, U32, cur), 0n, no, N, hN, hl) :
            {List.append(&2, U32, jl(List.reverse(&2, B.Ln, out)), List.append(&2, U32, List.reverse(&2, U32, cur), Con{10, B.uncr(t)})) ==
              List.append(&2, U32, List.append(&2, U32, jl(List.reverse(&2, B.Ln, out)), List.append(&2, U32, _, [10])), B.uncr(t)) : List<&2, U32>}
          %assoc_r(jl(List.reverse(&2, B.Ln, out)), List.append(&2, U32, List.reverse(&2, U32, cur), [10]), B.uncr(t)) :
            {List.append(&2, U32, jl(List.reverse(&2, B.Ln, out)), List.append(&2, U32, List.reverse(&2, U32, cur), Con{10, B.uncr(t)})) == _ : List<&2, U32>}
          %assoc_r(List.reverse(&2, U32, cur), [10], B.uncr(t)) :
            {List.append(&2, U32, jl(List.reverse(&2, B.Ln, out)), List.append(&2, U32, List.reverse(&2, U32, cur), Con{10, B.uncr(t)})) == List.append(&2, U32, jl(List.reverse(&2, B.Ln, out)), _) : List<&2, U32>}
          {==}
    case False{}:
      match b2:
        case True{}:
          ih_cr
        case False{}:
          %ih_ch : {List.append(&2, U32, jl(List.reverse(&2, B.Ln, out)), List.append(&2, U32, List.reverse(&2, U32, cur), Con{b, B.uncr(t)})) == _ : List<&2, U32>}
          %rev_snoc(cur, b) :
            {List.append(&2, U32, jl(List.reverse(&2, B.Ln, out)), List.append(&2, U32, List.reverse(&2, U32, cur), Con{b, B.uncr(t)})) ==
              List.append(&2, U32, jl(List.reverse(&2, B.Ln, out)), List.append(&2, U32, _, B.uncr(t))) : List<&2, U32>}
          %assoc_r(List.reverse(&2, U32, cur), [b], B.uncr(t)) :
            {List.append(&2, U32, jl(List.reverse(&2, B.Ln, out)), List.append(&2, U32, List.reverse(&2, U32, cur), Con{b, B.uncr(t)})) == List.append(&2, U32, jl(List.reverse(&2, B.Ln, out)), _) : List<&2, U32>}
          {==}

def lines_spec(bs: List<&2, U32>, +cur: List<&2, U32>, +no: U32, +out: List<&2, B.Ln>, +N: Nat, +hN: {N == Nat.pow(2n, 32n) : Nat}, +h: MNat.lt(Nat.add(List.length(&2, U32, cur), List.length(&2, U32, bs)), N)) ->
    {List.append(&2, U32, jl(List.reverse(&2, B.Ln, out)), List.append(&2, U32, List.reverse(&2, U32, cur), B.uncr(bs))) ==
      B.lines.text(B.lines.go(bs, cur, no, out)) : List<&2, U32>}:
  match bs:
    case Nil{}:
      lines_end(cur, no, out, N, hN, lim_rev(cur, N, lim_zero(List.length(&2, U32, cur), N, h)))
    case Con{+b, +t}:
      lines_step(b, t, cur, no, out, N, hN, U32.is_eq(b, 10), {==}, U32.is_eq(b, 13), {==},
        lim_rev(cur, N, lim_left(List.length(&2, U32, cur), 1n+List.length(&2, U32, t), N, h)),
        lines_spec(t, Nil{}, (no + 1 : U32), Con{B.lines.line(cur, no), out}, N, hN,
          lim_pred(List.length(&2, U32, t), N, lim_right(List.length(&2, U32, cur), 1n+List.length(&2, U32, t), N, h))),
        lines_spec(t, cur, no, out, N, hN, lim_pred(Nat.add(List.length(&2, U32, cur), List.length(&2, U32, t)), N, lim_succ(List.length(&2, U32, cur), List.length(&2, U32, t), N, h))),
        lines_spec(t, Con{b, cur}, no, out, N, hN, lim_succ(List.length(&2, U32, cur), List.length(&2, U32, t), N, h)))

# the law's bound in the form lines_spec takes, the bound abstract: Bend
# compares forms that differ by normalizing them, which unfolds 2^32
def top_bound(+bs: List<&2, U32>, +N: Nat, h: {Nat.is_lt(List.length(&2, U32, bs), N) == True{} : Bool}) ->
    MNat.lt(Nat.add(List.length(&2, U32, Nil{}), List.length(&2, U32, bs)), N):
  h

def Laws.lines.join(bs, h):
  Equal.sym(List<&2, U32>, B.uncr(bs), B.lines.text(B.lines(bs)),
    lines_spec(bs, Nil{}, (0 + 1 : U32), Nil{}, Nat.pow(2n, 32n), {==}, top_bound(bs, Nat.pow(2n, 32n), h)))

# The walk's order
# ----------------
#
# A unit joins the order only once its callees have (ds.done.k), so the
# order is callee-first after every step: each step keeps it or adds a
# unit whose callees are in it. Each step's choices are Bools its helpers
# match, which the lemmas split.

def call_keeps(+seen: Bool, +cyc: Bool, +c: U32, +u: U32, +rs: List<&2, U32>, +st: List<&2, B.Fm>, +roots: List<&2, U32>,
    +done: List<&2, U32>, +order: List<&2, U32>, +ers: List<&2, B.Er>, +cal: List<&2, List<&2, U32>>, +obs: List<&2, B.Ob>, +us: List<&2, B.Un>,
    +h: {B.ordered(order, cal) == True{} : Bool}) ->
    {B.ordered(B.ds.order(B.ds.call.k(seen, cyc, c, u, rs, st, roots, done, order, ers, cal, obs, us)), cal) == True{} : Bool}:
  match seen:
    case True{}:
      h
    case False{}:
      match cyc:
        case True{}:
          h
        case False{}:
          h

def done_keeps(+ok: Bool, +u: U32, +st: List<&2, B.Fm>, +roots: List<&2, U32>,
    +done: List<&2, U32>, +order: List<&2, U32>, +ers: List<&2, B.Er>, +cal: List<&2, List<&2, U32>>, +obs: List<&2, B.Ob>, +us: List<&2, B.Un>,
    +e: {ok == B.all.in(B.ids.at(cal, u), order) : Bool}, +h: {B.ordered(order, cal) == True{} : Bool}) ->
    {B.ordered(B.ds.order(B.ds.done.k(ok, u, st, roots, done, order, ers, obs, us)), cal) == True{} : Bool}:
  match ok:
    case True{}:
      %e : {Bool.and(_, B.ordered(order, cal)) == True{} : Bool}
      h
    case False{}:
      h

def root_keeps(+seen: Bool, +r: U32, +rt: List<&2, U32>, +done: List<&2, U32>, +order: List<&2, U32>, +ers: List<&2, B.Er>,
    +cal: List<&2, List<&2, U32>>, +h: {B.ordered(order, cal) == True{} : Bool}) ->
    {B.ordered(B.ds.order(B.ds.root.k(seen, r, rt, done, order, ers, cal)), cal) == True{} : Bool}:
  match seen:
    case True{}:
      h
    case False{}:
      h

def step_keeps(s: B.Ds, +cal: List<&2, List<&2, U32>>, +obs: List<&2, B.Ob>, +us: List<&2, B.Un>,
    +h: {B.ordered(B.ds.order(s), cal) == True{} : Bool}) ->
    {B.ordered(B.ds.order(B.ds.step(s, cal, obs, us)), cal) == True{} : Bool}:
  match s:
    case B.Ds{stack, +roots, +done, +order, +ers}:
      match stack:
        case Nil{}:
          match roots:
            case Nil{}:
              h
            case Con{+r, +rt}:
              root_keeps(B.has(done, r), r, rt, done, order, ers, cal, h)
        case Con{f, +st}:
          match f:
            case B.Fm{+u, rest}:
              match rest:
                case Nil{}:
                  done_keeps(B.all.in(B.ids.at(cal, u), order), u, st, roots, done, order, ers, cal, obs, us, {==}, h)
                case Con{+c, rs}:
                  call_keeps(B.has(done, c), B.has(Con{u, B.fms.units(st)}, c), c, u, rs, st, roots, done, order, ers, cal, obs, us, h)

def go_keeps(n: Nat, +s: B.Ds, +cal: List<&2, List<&2, U32>>, +obs: List<&2, B.Ob>, +us: List<&2, B.Un>,
    +h: {B.ordered(B.ds.order(s), cal) == True{} : Bool}) ->
    {B.ordered(B.ds.order(B.ds.go(n, s, cal, obs, us)), cal) == True{} : Bool}:
  match n:
    case 0n:
      h
    case 1n+k:
      go_keeps(k, B.ds.step(s, cal, obs, us), cal, obs, us, step_keeps(s, cal, obs, us, h))

def Laws.order.callees_first(roots, cal, obs, us):
  go_keeps(B.walk.fuel(roots, cal),
    B.Ds{Nil{}, roots, Nil{}, Nil{}, Nil{}}, cal, obs, us, {==})

# The walk's order, each unit once
# --------------------------------
#
# The invariant: the order is distinct, every unit in it walked; the
# units on the stack distinct, none walked. A unit is pushed only when
# neither walked nor on the stack, and joins the order when popped, so
# once.

def and_intro(+a: Bool, +b: Bool, pa: {a == True{} : Bool}, pb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, pa) : {Bool.and(_, b) == True{} : Bool}
  pb

def or_false_l(+a: Bool, +b: Bool, h: {Bool.or(a, b) == False{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, MB.true_ne_false()(h))
    case False{}:
      {==}

def or_false_r(+a: Bool, +b: Bool, h: {Bool.or(a, b) == False{} : Bool}) -> {b == False{} : Bool}:
  match a:
    case True{}:
      Empty.absurd({b == False{} : Bool}, MB.true_ne_false()(h))
    case False{}:
      h

def not_true(+b: Bool, h: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, MB.false_ne_true()(h))
    case False{}:
      {==}

def u32_is_eq_comm(+a: U32, +b: U32) -> {U32.is_eq(a, b) == U32.is_eq(b, a) : Bool}:
  Equal.trans(Bool, U32.is_eq(a, b), Nat.is_eq(U32.to_nat(a), U32.to_nat(b)), U32.is_eq(b, a), MU.u32_is_eq_to_nat(a, b),
    Equal.trans(Bool, Nat.is_eq(U32.to_nat(a), U32.to_nat(b)), Nat.is_eq(U32.to_nat(b), U32.to_nat(a)), U32.is_eq(b, a),
      MNat.is_eq_comm(U32.to_nat(a), U32.to_nat(b)), MU.u32_is_eq_to_nat_sym(b, a)))

def has_self(+done: List<&2, U32>, +u: U32) -> {B.has(Con{u, done}, u) == True{} : Bool}:
  %Equal.sym(Bool, U32.is_eq(u, u), True{}, u32_is_eq_refl(u)) : {Bool.or(_, B.has(done, u)) == True{} : Bool}
  {==}

def has_mono(+xs: List<&2, U32>, +u: U32, +x: U32, h: {B.has(xs, x) == True{} : Bool}) -> {B.has(Con{u, xs}, x) == True{} : Bool}:
  %Equal.sym(Bool, B.has(xs, x), True{}, h) : {Bool.or(U32.is_eq(u, x), _) == True{} : Bool}
  MB.or_true(U32.is_eq(u, x))

def all_in_mono(ys: List<&2, U32>, +done: List<&2, U32>, +u: U32, +h: {B.all.in(ys, done) == True{} : Bool}) -> {B.all.in(ys, Con{u, done}) == True{} : Bool}:
  match ys:
    case Nil{}:
      {==}
    case Con{+y, +t}:
      and_intro(B.has(Con{u, done}, y), B.all.in(t, Con{u, done}),
        has_mono(done, u, y, MB.eq_true_of_and_left(B.has(done, y), B.all.in(t, done), h)),
        all_in_mono(t, done, u, MB.eq_true_of_and_right(B.has(done, y), B.all.in(t, done), h)))

def none_in(xs: List<&2, U32>, +done: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, t}:
      Bool.and(Bool.not(B.has(done, x)), none_in(t, done))

# a unit not walked is not in the order, which holds only units walked
def sub_step(+y: U32, +t: List<&2, U32>, +done: List<&2, U32>, +u: U32, b: Bool, +e: {b == U32.is_eq(y, u) : Bool},
    hy: {B.has(done, y) == True{} : Bool}, +hn: {B.has(done, u) == False{} : Bool}, ih: {B.has(t, u) == False{} : Bool}) ->
    {Bool.or(b, B.has(t, u)) == False{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({Bool.or(True{}, B.has(t, u)) == False{} : Bool},
        MB.true_ne_false()(Equal.trans(Bool, True{}, B.has(done, u), False{},
          Equal.sym(Bool, B.has(done, u), True{},
            ME.subst(U32, x => {B.has(done, x) == True{} : Bool}, y, u, u32_eq_of_is_eq(y, u, Equal.sym(Bool, True{}, U32.is_eq(y, u), e)), hy)),
          hn)))
    case False{}:
      ih

def not_in_of_sub(ys: List<&2, U32>, +done: List<&2, U32>, +u: U32, +hsub: {B.all.in(ys, done) == True{} : Bool}, +hn: {B.has(done, u) == False{} : Bool}) ->
    {B.has(ys, u) == False{} : Bool}:
  match ys:
    case Nil{}:
      {==}
    case Con{+y, +t}:
      sub_step(y, t, done, u, U32.is_eq(y, u), {==}, MB.eq_true_of_and_left(B.has(done, y), B.all.in(t, done), hsub), hn,
        not_in_of_sub(t, done, u, MB.eq_true_of_and_right(B.has(done, y), B.all.in(t, done), hsub), hn))

# units none walked, u not among them: none walked once u is
def none_in_extend(xs: List<&2, U32>, +done: List<&2, U32>, +u: U32, +hn: {none_in(xs, done) == True{} : Bool}, +hu: {B.has(xs, u) == False{} : Bool}) ->
    {none_in(xs, Con{u, done}) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %Equal.trans(Bool, False{}, U32.is_eq(x, u), U32.is_eq(u, x),
          Equal.sym(Bool, U32.is_eq(x, u), False{}, or_false_l(U32.is_eq(x, u), B.has(t, u), hu)), u32_is_eq_comm(x, u)) :
        {Bool.and(Bool.not(Bool.or(_, B.has(done, x))), none_in(t, Con{u, done})) == True{} : Bool}
      %Equal.sym(Bool, B.has(done, x), False{}, not_true(B.has(done, x), MB.eq_true_of_and_left(Bool.not(B.has(done, x)), none_in(t, done), hn))) :
        {Bool.and(Bool.not(Bool.or(False{}, _)), none_in(t, Con{u, done})) == True{} : Bool}
      none_in_extend(t, done, u, MB.eq_true_of_and_right(Bool.not(B.has(done, x)), none_in(t, done), hn), or_false_r(U32.is_eq(x, u), B.has(t, u), hu))

def inv4(+order: List<&2, U32>, +done: List<&2, U32>, +st: List<&2, B.Fm>) -> Bool:
  Bool.and(B.distinct(order), Bool.and(B.all.in(order, done), Bool.and(none_in(B.fms.units(st), done), B.distinct(B.fms.units(st)))))

def inv(s: B.Ds) -> Bool:
  match s:
    case B.Ds{stack, roots, done, order, ers}:
      inv4(order, done, stack)

def mk4(+order: List<&2, U32>, +done: List<&2, U32>, +st: List<&2, B.Fm>,
    pa: {B.distinct(order) == True{} : Bool}, pb: {B.all.in(order, done) == True{} : Bool},
    pc: {none_in(B.fms.units(st), done) == True{} : Bool}, pd: {B.distinct(B.fms.units(st)) == True{} : Bool}) -> {inv4(order, done, st) == True{} : Bool}:
  and_intro(B.distinct(order), Bool.and(B.all.in(order, done), Bool.and(none_in(B.fms.units(st), done), B.distinct(B.fms.units(st)))), pa,
    and_intro(B.all.in(order, done), Bool.and(none_in(B.fms.units(st), done), B.distinct(B.fms.units(st))), pb,
      and_intro(none_in(B.fms.units(st), done), B.distinct(B.fms.units(st)), pc, pd)))

def get_a(+order: List<&2, U32>, +done: List<&2, U32>, +st: List<&2, B.Fm>, h: {inv4(order, done, st) == True{} : Bool}) -> {B.distinct(order) == True{} : Bool}:
  MB.eq_true_of_and_left(B.distinct(order), Bool.and(B.all.in(order, done), Bool.and(none_in(B.fms.units(st), done), B.distinct(B.fms.units(st)))), h)

def get_bcd(+order: List<&2, U32>, +done: List<&2, U32>, +st: List<&2, B.Fm>, h: {inv4(order, done, st) == True{} : Bool}) ->
    {Bool.and(B.all.in(order, done), Bool.and(none_in(B.fms.units(st), done), B.distinct(B.fms.units(st)))) == True{} : Bool}:
  MB.eq_true_of_and_right(B.distinct(order), Bool.and(B.all.in(order, done), Bool.and(none_in(B.fms.units(st), done), B.distinct(B.fms.units(st)))), h)

def get_b(+order: List<&2, U32>, +done: List<&2, U32>, +st: List<&2, B.Fm>, h: {inv4(order, done, st) == True{} : Bool}) -> {B.all.in(order, done) == True{} : Bool}:
  MB.eq_true_of_and_left(B.all.in(order, done), Bool.and(none_in(B.fms.units(st), done), B.distinct(B.fms.units(st))), get_bcd(order, done, st, h))

def get_c(+order: List<&2, U32>, +done: List<&2, U32>, +st: List<&2, B.Fm>, h: {inv4(order, done, st) == True{} : Bool}) -> {none_in(B.fms.units(st), done) == True{} : Bool}:
  MB.eq_true_of_and_left(none_in(B.fms.units(st), done), B.distinct(B.fms.units(st)),
    MB.eq_true_of_and_right(B.all.in(order, done), Bool.and(none_in(B.fms.units(st), done), B.distinct(B.fms.units(st))), get_bcd(order, done, st, h)))

def get_d(+order: List<&2, U32>, +done: List<&2, U32>, +st: List<&2, B.Fm>, h: {inv4(order, done, st) == True{} : Bool}) -> {B.distinct(B.fms.units(st)) == True{} : Bool}:
  MB.eq_true_of_and_right(none_in(B.fms.units(st), done), B.distinct(B.fms.units(st)),
    MB.eq_true_of_and_right(B.all.in(order, done), Bool.and(none_in(B.fms.units(st), done), B.distinct(B.fms.units(st))), get_bcd(order, done, st, h)))

def root_once(+seen: Bool, +r: U32, +rt: List<&2, U32>, +done: List<&2, U32>, +order: List<&2, U32>, +ers: List<&2, B.Er>, +cal: List<&2, List<&2, U32>>,
    +e: {seen == B.has(done, r) : Bool}, +h: {inv4(order, done, Nil{}) == True{} : Bool}) ->
    {inv(B.ds.root.k(seen, r, rt, done, order, ers, cal)) == True{} : Bool}:
  match seen:
    case True{}:
      h
    case False{}:
      mk4(order, done, [B.Fm{r, B.ids.at(cal, r)}], get_a(order, done, Nil{}, h), get_b(order, done, Nil{}, h),
        and_intro(Bool.not(B.has(done, r)), True{}, Equal.sym(Bool, True{}, Bool.not(B.has(done, r)),
          ME.subst(Bool, x => {True{} == Bool.not(x) : Bool}, False{}, B.has(done, r), e, {==})), {==}),
        {==})

def call_once(+seen: Bool, +cyc: Bool, +c: U32, +u: U32, +rs: List<&2, U32>, +st: List<&2, B.Fm>, +roots: List<&2, U32>,
    +done: List<&2, U32>, +order: List<&2, U32>, +ers: List<&2, B.Er>, +cal: List<&2, List<&2, U32>>, +obs: List<&2, B.Ob>, +us: List<&2, B.Un>,
    +e1: {seen == B.has(done, c) : Bool}, +e2: {cyc == B.has(Con{u, B.fms.units(st)}, c) : Bool},
    +h: {inv4(order, done, Con{B.Fm{u, Con{c, rs}}, st}) == True{} : Bool}) ->
    {inv(B.ds.call.k(seen, cyc, c, u, rs, st, roots, done, order, ers, cal, obs, us)) == True{} : Bool}:
  match seen:
    case True{}:
      h
    case False{}:
      match cyc:
        case True{}:
          h
        case False{}:
          mk4(order, done, Con{B.Fm{c, B.ids.at(cal, c)}, Con{B.Fm{u, rs}, st}},
            get_a(order, done, Con{B.Fm{u, Con{c, rs}}, st}, h), get_b(order, done, Con{B.Fm{u, Con{c, rs}}, st}, h),
            and_intro(Bool.not(B.has(done, c)), none_in(Con{u, B.fms.units(st)}, done),
              ME.subst(Bool, x => {Bool.not(x) == True{} : Bool}, False{}, B.has(done, c), e1, {==}),
              get_c(order, done, Con{B.Fm{u, Con{c, rs}}, st}, h)),
            and_intro(Bool.not(B.has(Con{u, B.fms.units(st)}, c)), B.distinct(Con{u, B.fms.units(st)}),
              ME.subst(Bool, x => {Bool.not(x) == True{} : Bool}, False{}, B.has(Con{u, B.fms.units(st)}, c), e2, {==}),
              get_d(order, done, Con{B.Fm{u, Con{c, rs}}, st}, h)))

# a unit popped: walked now, and joined to the order or held back
def done_once.k(+ok: Bool, +u: U32, +st: List<&2, B.Fm>, +roots: List<&2, U32>, +done: List<&2, U32>, +order: List<&2, U32>,
    +ers: List<&2, B.Er>, +obs: List<&2, B.Ob>, +us: List<&2, B.Un>,
    +ha: {B.distinct(order) == True{} : Bool}, +hb: {B.all.in(order, done) == True{} : Bool}, +hu: {B.has(done, u) == False{} : Bool},
    +hst: {none_in(B.fms.units(st), done) == True{} : Bool}, +hnu: {B.has(B.fms.units(st), u) == False{} : Bool},
    +hds: {B.distinct(B.fms.units(st)) == True{} : Bool}) ->
    {inv(B.ds.done.k(ok, u, st, roots, done, order, ers, obs, us)) == True{} : Bool}:
  match ok:
    case True{}:
      mk4(Con{u, order}, Con{u, done}, st,
        and_intro(Bool.not(B.has(order, u)), B.distinct(order),
          ME.subst(Bool, x => {Bool.not(x) == True{} : Bool}, False{}, B.has(order, u),
            Equal.sym(Bool, B.has(order, u), False{}, not_in_of_sub(order, done, u, hb, hu)), {==}), ha),
        and_intro(B.has(Con{u, done}, u), B.all.in(order, Con{u, done}), has_self(done, u), all_in_mono(order, done, u, hb)),
        none_in_extend(B.fms.units(st), done, u, hst, hnu),
        hds)
    case False{}:
      mk4(order, Con{u, done}, st, ha, all_in_mono(order, done, u, hb), none_in_extend(B.fms.units(st), done, u, hst, hnu), hds)

def done_once(+ok: Bool, +u: U32, +st: List<&2, B.Fm>, +roots: List<&2, U32>, +done: List<&2, U32>, +order: List<&2, U32>,
    +ers: List<&2, B.Er>, +obs: List<&2, B.Ob>, +us: List<&2, B.Un>,
    +h: {inv4(order, done, Con{B.Fm{u, Nil{}}, st}) == True{} : Bool}) ->
    {inv(B.ds.done.k(ok, u, st, roots, done, order, ers, obs, us)) == True{} : Bool}:
  +hc = get_c(order, done, Con{B.Fm{u, Nil{}}, st}, h)
  +hd = get_d(order, done, Con{B.Fm{u, Nil{}}, st}, h)
  +hu = not_true(B.has(done, u), MB.eq_true_of_and_left(Bool.not(B.has(done, u)), none_in(B.fms.units(st), done), hc))
  +hst = MB.eq_true_of_and_right(Bool.not(B.has(done, u)), none_in(B.fms.units(st), done), hc)
  +hnu = not_true(B.has(B.fms.units(st), u), MB.eq_true_of_and_left(Bool.not(B.has(B.fms.units(st), u)), B.distinct(B.fms.units(st)), hd))
  +hds = MB.eq_true_of_and_right(Bool.not(B.has(B.fms.units(st), u)), B.distinct(B.fms.units(st)), hd)
  +hb = get_b(order, done, Con{B.Fm{u, Nil{}}, st}, h)
  done_once.k(ok, u, st, roots, done, order, ers, obs, us, get_a(order, done, Con{B.Fm{u, Nil{}}, st}, h), hb, hu, hst, hnu, hds)

def step_once(s: B.Ds, +cal: List<&2, List<&2, U32>>, +obs: List<&2, B.Ob>, +us: List<&2, B.Un>, +h: {inv(s) == True{} : Bool}) ->
    {inv(B.ds.step(s, cal, obs, us)) == True{} : Bool}:
  match s:
    case B.Ds{stack, +roots, +done, +order, +ers}:
      match stack:
        case Nil{}:
          match roots:
            case Nil{}:
              h
            case Con{+r, +rt}:
              root_once(B.has(done, r), r, rt, done, order, ers, cal, {==}, h)
        case Con{f, +st}:
          match f:
            case B.Fm{+u, rest}:
              match rest:
                case Nil{}:
                  done_once(B.all.in(B.ids.at(cal, u), order), u, st, roots, done, order, ers, obs, us, h)
                case Con{+c, +rs}:
                  call_once(B.has(done, c), B.has(Con{u, B.fms.units(st)}, c), c, u, rs, st, roots, done, order, ers, cal, obs, us, {==}, {==}, h)

def go_once(n: Nat, +s: B.Ds, +cal: List<&2, List<&2, U32>>, +obs: List<&2, B.Ob>, +us: List<&2, B.Un>, +h: {inv(s) == True{} : Bool}) ->
    {inv(B.ds.go(n, s, cal, obs, us)) == True{} : Bool}:
  match n:
    case 0n:
      h
    case 1n+k:
      go_once(k, B.ds.step(s, cal, obs, us), cal, obs, us, step_once(s, cal, obs, us, h))

def inv_order(s: B.Ds, h: {inv(s) == True{} : Bool}) -> {B.distinct(B.ds.order(s)) == True{} : Bool}:
  match s:
    case B.Ds{stack, roots, +done, +order, ers}:
      get_a(order, done, stack, h)

def Laws.order.once(roots, cal, obs, us):
  inv_order(B.walk(roots, cal, obs, us),
    go_once(B.walk.fuel(roots, cal),
      B.Ds{Nil{}, roots, Nil{}, Nil{}, Nil{}}, cal, obs, us, {==}))

# The walk's order, nothing walked lost
# -------------------------------------
#
# The invariant: an error is reported, or every unit walked is in the
# order. A unit held back reports an error where none was, and errors
# are never taken back.

def jinv(s: B.Ds) -> Bool:
  match s:
    case B.Ds{stack, roots, done, order, ers}:
      Bool.or(Bool.not(List.is_empty(&2, B.Er, ers)), B.all.in(done, order))

def done_walked(+ok: Bool, +u: U32, +st: List<&2, B.Fm>, +roots: List<&2, U32>, +done: List<&2, U32>, +order: List<&2, U32>,
    +ers: List<&2, B.Er>, +obs: List<&2, B.Ob>, +us: List<&2, B.Un>,
    +h: {Bool.or(Bool.not(List.is_empty(&2, B.Er, ers)), B.all.in(done, order)) == True{} : Bool}) ->
    {jinv(B.ds.done.k(ok, u, st, roots, done, order, ers, obs, us)) == True{} : Bool}:
  match ok:
    case True{}:
      match ers:
        case Nil{}:
          and_intro(B.has(Con{u, order}, u), B.all.in(done, Con{u, order}), has_self(order, u), all_in_mono(done, order, u, h))
        case Con{e, es}:
          {==}
    case False{}:
      match ers:
        case Nil{}:
          {==}
        case Con{e, es}:
          {==}

def root_walked(+seen: Bool, +r: U32, +rt: List<&2, U32>, +done: List<&2, U32>, +order: List<&2, U32>, +ers: List<&2, B.Er>, +cal: List<&2, List<&2, U32>>,
    +h: {Bool.or(Bool.not(List.is_empty(&2, B.Er, ers)), B.all.in(done, order)) == True{} : Bool}) ->
    {jinv(B.ds.root.k(seen, r, rt, done, order, ers, cal)) == True{} : Bool}:
  match seen:
    case True{}:
      h
    case False{}:
      h

def call_walked(+seen: Bool, +cyc: Bool, +c: U32, +u: U32, +rs: List<&2, U32>, +st: List<&2, B.Fm>, +roots: List<&2, U32>,
    +done: List<&2, U32>, +order: List<&2, U32>, +ers: List<&2, B.Er>, +cal: List<&2, List<&2, U32>>, +obs: List<&2, B.Ob>, +us: List<&2, B.Un>,
    +h: {Bool.or(Bool.not(List.is_empty(&2, B.Er, ers)), B.all.in(done, order)) == True{} : Bool}) ->
    {jinv(B.ds.call.k(seen, cyc, c, u, rs, st, roots, done, order, ers, cal, obs, us)) == True{} : Bool}:
  match seen:
    case True{}:
      h
    case False{}:
      match cyc:
        case True{}:
          {==}
        case False{}:
          h

def step_walked(s: B.Ds, +cal: List<&2, List<&2, U32>>, +obs: List<&2, B.Ob>, +us: List<&2, B.Un>, +h: {jinv(s) == True{} : Bool}) ->
    {jinv(B.ds.step(s, cal, obs, us)) == True{} : Bool}:
  match s:
    case B.Ds{stack, +roots, +done, +order, +ers}:
      match stack:
        case Nil{}:
          match roots:
            case Nil{}:
              h
            case Con{+r, +rt}:
              root_walked(B.has(done, r), r, rt, done, order, ers, cal, h)
        case Con{f, +st}:
          match f:
            case B.Fm{+u, rest}:
              match rest:
                case Nil{}:
                  done_walked(B.all.in(B.ids.at(cal, u), order), u, st, roots, done, order, ers, obs, us, h)
                case Con{+c, +rs}:
                  call_walked(B.has(done, c), B.has(Con{u, B.fms.units(st)}, c), c, u, rs, st, roots, done, order, ers, cal, obs, us, h)

def go_walked(n: Nat, +s: B.Ds, +cal: List<&2, List<&2, U32>>, +obs: List<&2, B.Ob>, +us: List<&2, B.Un>, +h: {jinv(s) == True{} : Bool}) ->
    {jinv(B.ds.go(n, s, cal, obs, us)) == True{} : Bool}:
  match n:
    case 0n:
      h
    case 1n+k:
      go_walked(k, B.ds.step(s, cal, obs, us), cal, obs, us, step_walked(s, cal, obs, us, h))

# no error reported: every unit walked in the order
def jinv_out(s: B.Ds, h: {jinv(s) == True{} : Bool}, +e: {List.is_empty(&2, B.Er, B.ds.ers(s)) == True{} : Bool}) ->
    {B.all.in(B.ds.walked(s), B.ds.order(s)) == True{} : Bool}:
  match s:
    case B.Ds{stack, roots, +done, +order, +ers}:
      ME.subst(Bool, x => {Bool.or(Bool.not(x), B.all.in(done, order)) == True{} : Bool}, List.is_empty(&2, B.Er, ers), True{}, e, h)

def Laws.order.walked(roots, cal, obs, us, h):
  jinv_out(B.walk(roots, cal, obs, us),
    go_walked(B.walk.fuel(roots, cal),
      B.Ds{Nil{}, roots, Nil{}, Nil{}, Nil{}}, cal, obs, us, {==}), h)

# The walk's roots, every one walked
# ----------------------------------
#
# The invariant: every root is among the units on the stack, those
# walked and the roots left (cov); each step keeps every unit of the one
# among the next's. Containment is a Bool (all.in), reusable where a
# proof function is not.

def or_cases(+a: Bool, +b: Bool, +c: Bool, h: {Bool.or(a, b) == True{} : Bool},
    fa: {a == True{} : Bool} -> {c == True{} : Bool}, fb: {b == True{} : Bool} -> {c == True{} : Bool}) -> {c == True{} : Bool}:
  match a:
    case True{}:
      fa({==})
    case False{}:
      fb(h)

def has_sub(xs: List<&2, U32>, +ys: List<&2, U32>, +x: U32, +hs: {B.all.in(xs, ys) == True{} : Bool}, hx: {B.has(xs, x) == True{} : Bool}) ->
    {B.has(ys, x) == True{} : Bool}:
  match xs:
    case Nil{}:
      Empty.absurd({B.has(ys, x) == True{} : Bool}, MB.false_ne_true()(hx))
    case Con{+y, +t}:
      +hy = MB.eq_true_of_and_left(B.has(ys, y), B.all.in(t, ys), hs)
      +ht = MB.eq_true_of_and_right(B.has(ys, y), B.all.in(t, ys), hs)
      or_cases(U32.is_eq(y, x), B.has(t, x), B.has(ys, x), hx,
        e => ME.subst(U32, z => {B.has(ys, z) == True{} : Bool}, y, x, u32_eq_of_is_eq(y, x, e), hy),
        hh => has_sub(t, ys, x, ht, hh))

def sub_trans(r: List<&2, U32>, +xs: List<&2, U32>, +ys: List<&2, U32>, +h1: {B.all.in(r, xs) == True{} : Bool}, +h2: {B.all.in(xs, ys) == True{} : Bool}) ->
    {B.all.in(r, ys) == True{} : Bool}:
  match r:
    case Nil{}:
      {==}
    case Con{+a, +t}:
      and_intro(B.has(ys, a), B.all.in(t, ys), has_sub(xs, ys, a, h2, MB.eq_true_of_and_left(B.has(xs, a), B.all.in(t, xs), h1)),
        sub_trans(t, xs, ys, MB.eq_true_of_and_right(B.has(xs, a), B.all.in(t, xs), h1), h2))

def sub_refl(xs: List<&2, U32>) -> {B.all.in(xs, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+a, +t}:
      and_intro(B.has(Con{a, t}, a), B.all.in(t, Con{a, t}), has_self(t, a), all_in_mono(t, t, a, sub_refl(t)))

def sub_cons(+xs: List<&2, U32>, +u: U32) -> {B.all.in(xs, Con{u, xs}) == True{} : Bool}:
  all_in_mono(xs, xs, u, sub_refl(xs))

def sub_l(p: List<&2, U32>, +q: List<&2, U32>) -> {B.all.in(p, List.append(&2, U32, p, q)) == True{} : Bool}:
  match p:
    case Nil{}:
      {==}
    case Con{+a, +t}:
      and_intro(B.has(Con{a, List.append(&2, U32, t, q)}, a), B.all.in(t, Con{a, List.append(&2, U32, t, q)}),
        has_self(List.append(&2, U32, t, q), a), all_in_mono(t, List.append(&2, U32, t, q), a, sub_l(t, q)))

def sub_r(p: List<&2, U32>, +q: List<&2, U32>) -> {B.all.in(q, List.append(&2, U32, p, q)) == True{} : Bool}:
  match p:
    case Nil{}:
      sub_refl(q)
    case Con{+a, +t}:
      all_in_mono(q, List.append(&2, U32, t, q), a, sub_r(t, q))

def sub_app(p: List<&2, U32>, +q: List<&2, U32>, +ys: List<&2, U32>, +hp: {B.all.in(p, ys) == True{} : Bool}, +hq: {B.all.in(q, ys) == True{} : Bool}) ->
    {B.all.in(List.append(&2, U32, p, q), ys) == True{} : Bool}:
  match p:
    case Nil{}:
      hq
    case Con{+a, +t}:
      and_intro(B.has(ys, a), B.all.in(List.append(&2, U32, t, q), ys), MB.eq_true_of_and_left(B.has(ys, a), B.all.in(t, ys), hp),
        sub_app(t, q, ys, MB.eq_true_of_and_right(B.has(ys, a), B.all.in(t, ys), hp), hq))

# a unit in p is in p ++ q
def in_l(+p: List<&2, U32>, +q: List<&2, U32>, +x: U32, +h: {B.has(p, x) == True{} : Bool}) -> {B.has(List.append(&2, U32, p, q), x) == True{} : Bool}:
  has_sub(p, List.append(&2, U32, p, q), x, sub_l(p, q), h)

def cov(s: B.Ds) -> List<&2, U32>:
  match s:
    case B.Ds{stack, roots, done, order, ers}:
      List.append(&2, U32, B.fms.units(stack), List.append(&2, U32, done, roots))

def root_roots(+seen: Bool, +r: U32, +rt: List<&2, U32>, +done: List<&2, U32>, +order: List<&2, U32>, +ers: List<&2, B.Er>, +cal: List<&2, List<&2, U32>>,
    +e: {seen == B.has(done, r) : Bool}, +rs0: List<&2, U32>, +h: {B.all.in(rs0, List.append(&2, U32, done, Con{r, rt})) == True{} : Bool}) ->
    {B.all.in(rs0, cov(B.ds.root.k(seen, r, rt, done, order, ers, cal))) == True{} : Bool}:
  match seen:
    case True{}:
      sub_trans(rs0, List.append(&2, U32, done, Con{r, rt}), List.append(&2, U32, done, rt), h,
        sub_app(done, Con{r, rt}, List.append(&2, U32, done, rt), sub_l(done, rt),
          and_intro(B.has(List.append(&2, U32, done, rt), r), B.all.in(rt, List.append(&2, U32, done, rt)),
            in_l(done, rt, r, Equal.sym(Bool, True{}, B.has(done, r), e)), sub_r(done, rt))))
    case False{}:
      sub_trans(rs0, List.append(&2, U32, done, Con{r, rt}), Con{r, List.append(&2, U32, done, rt)}, h,
        sub_app(done, Con{r, rt}, Con{r, List.append(&2, U32, done, rt)},
          all_in_mono(done, List.append(&2, U32, done, rt), r, sub_l(done, rt)),
          and_intro(B.has(Con{r, List.append(&2, U32, done, rt)}, r), B.all.in(rt, Con{r, List.append(&2, U32, done, rt)}),
            has_self(List.append(&2, U32, done, rt), r), all_in_mono(rt, List.append(&2, U32, done, rt), r, sub_r(done, rt)))))

def call_roots(+seen: Bool, +cyc: Bool, +c: U32, +u: U32, +rs: List<&2, U32>, +st: List<&2, B.Fm>, +roots: List<&2, U32>,
    +done: List<&2, U32>, +order: List<&2, U32>, +ers: List<&2, B.Er>, +cal: List<&2, List<&2, U32>>, +obs: List<&2, B.Ob>, +us: List<&2, B.Un>,
    +rs0: List<&2, U32>, +h: {B.all.in(rs0, Con{u, List.append(&2, U32, B.fms.units(st), List.append(&2, U32, done, roots))}) == True{} : Bool}) ->
    {B.all.in(rs0, cov(B.ds.call.k(seen, cyc, c, u, rs, st, roots, done, order, ers, cal, obs, us))) == True{} : Bool}:
  match seen:
    case True{}:
      h
    case False{}:
      match cyc:
        case True{}:
          h
        case False{}:
          sub_trans(rs0, Con{u, List.append(&2, U32, B.fms.units(st), List.append(&2, U32, done, roots))},
            Con{c, Con{u, List.append(&2, U32, B.fms.units(st), List.append(&2, U32, done, roots))}}, h,
            sub_cons(Con{u, List.append(&2, U32, B.fms.units(st), List.append(&2, U32, done, roots))}, c))

# a unit popped: from the stack to those walked
def pop_sub(+u: U32, +a: List<&2, U32>, +d: List<&2, U32>) ->
    {B.all.in(Con{u, List.append(&2, U32, a, d)}, List.append(&2, U32, a, Con{u, d})) == True{} : Bool}:
  and_intro(B.has(List.append(&2, U32, a, Con{u, d}), u), B.all.in(List.append(&2, U32, a, d), List.append(&2, U32, a, Con{u, d})),
    has_sub(Con{u, d}, List.append(&2, U32, a, Con{u, d}), u, sub_r(a, Con{u, d}), has_self(d, u)),
    sub_app(a, d, List.append(&2, U32, a, Con{u, d}), sub_l(a, Con{u, d}),
      sub_trans(d, Con{u, d}, List.append(&2, U32, a, Con{u, d}), sub_cons(d, u), sub_r(a, Con{u, d}))))

def done_roots(+ok: Bool, +u: U32, +st: List<&2, B.Fm>, +roots: List<&2, U32>, +done: List<&2, U32>, +order: List<&2, U32>,
    +ers: List<&2, B.Er>, +obs: List<&2, B.Ob>, +us: List<&2, B.Un>,
    +rs0: List<&2, U32>, +h: {B.all.in(rs0, Con{u, List.append(&2, U32, B.fms.units(st), List.append(&2, U32, done, roots))}) == True{} : Bool}) ->
    {B.all.in(rs0, cov(B.ds.done.k(ok, u, st, roots, done, order, ers, obs, us))) == True{} : Bool}:
  match ok:
    case True{}:
      sub_trans(rs0, Con{u, List.append(&2, U32, B.fms.units(st), List.append(&2, U32, done, roots))},
        List.append(&2, U32, B.fms.units(st), Con{u, List.append(&2, U32, done, roots)}), h,
        pop_sub(u, B.fms.units(st), List.append(&2, U32, done, roots)))
    case False{}:
      sub_trans(rs0, Con{u, List.append(&2, U32, B.fms.units(st), List.append(&2, U32, done, roots))},
        List.append(&2, U32, B.fms.units(st), Con{u, List.append(&2, U32, done, roots)}), h,
        pop_sub(u, B.fms.units(st), List.append(&2, U32, done, roots)))

def step_roots(s: B.Ds, +cal: List<&2, List<&2, U32>>, +obs: List<&2, B.Ob>, +us: List<&2, B.Un>, +rs0: List<&2, U32>,
    +h: {B.all.in(rs0, cov(s)) == True{} : Bool}) -> {B.all.in(rs0, cov(B.ds.step(s, cal, obs, us))) == True{} : Bool}:
  match s:
    case B.Ds{stack, +roots, +done, +order, +ers}:
      match stack:
        case Nil{}:
          match roots:
            case Nil{}:
              h
            case Con{+r, +rt}:
              root_roots(B.has(done, r), r, rt, done, order, ers, cal, {==}, rs0, h)
        case Con{f, +st}:
          match f:
            case B.Fm{+u, rest}:
              match rest:
                case Nil{}:
                  done_roots(B.all.in(B.ids.at(cal, u), order), u, st, roots, done, order, ers, obs, us, rs0, h)
                case Con{+c, +rs}:
                  call_roots(B.has(done, c), B.has(Con{u, B.fms.units(st)}, c), c, u, rs, st, roots, done, order, ers, cal, obs, us, rs0, h)

def go_roots(n: Nat, +s: B.Ds, +cal: List<&2, List<&2, U32>>, +obs: List<&2, B.Ob>, +us: List<&2, B.Un>, +rs0: List<&2, U32>,
    +h: {B.all.in(rs0, cov(s)) == True{} : Bool}) -> {B.all.in(rs0, cov(B.ds.go(n, s, cal, obs, us))) == True{} : Bool}:
  match n:
    case 0n:
      h
    case 1n+k:
      go_roots(k, B.ds.step(s, cal, obs, us), cal, obs, us, rs0, step_roots(s, cal, obs, us, rs0, h))

# finished: no stack, no roots, so every root walked
def roots_out(s: B.Ds, +rs0: List<&2, U32>, +h: {B.all.in(rs0, cov(s)) == True{} : Bool}, e: {B.ds.finished(s) == True{} : Bool}) ->
    {B.all.in(rs0, B.ds.walked(s)) == True{} : Bool}:
  match s:
    case B.Ds{stack, roots, +done, order, ers}:
      match stack:
        case Nil{}:
          match roots:
            case Nil{}:
              sub_trans(rs0, List.append(&2, U32, done, Nil{}), done, h, sub_app(done, Nil{}, done, sub_refl(done), {==}))
            case Con{r, rt}:
              Empty.absurd({B.all.in(rs0, done) == True{} : Bool}, MB.false_ne_true()(e))
        case Con{f, st}:
          Empty.absurd({B.all.in(rs0, done) == True{} : Bool}, MB.false_ne_true()(e))

def Laws.order.roots(roots, cal, obs, us, h):
  roots_out(B.walk(roots, cal, obs, us), roots,
    go_roots(B.walk.fuel(roots, cal),
      B.Ds{Nil{}, roots, Nil{}, Nil{}, Nil{}}, cal, obs, us, roots, sub_refl(roots)), h)

# The walk's calls, every one walked
# ----------------------------------
#
# The invariant, c the stack's units then those walked: every walked
# unit's callees among c; each frame's callees among c or still to follow
# (its rest). A call followed joins c (walked, on the stack, or pushed);
# a unit popped has followed all, so its callees are among c.

def frames_ok(st: List<&2, B.Fm>, +cal: List<&2, List<&2, U32>>, +c: List<&2, U32>) -> Bool:
  match st:
    case Nil{}:
      True{}
    case Con{f, t}:
      match f:
        case B.Fm{+u, rest}:
          Bool.and(B.all.in(B.ids.at(cal, u), List.append(&2, U32, c, rest)), frames_ok(t, cal, c))

def kinv4(+cal: List<&2, List<&2, U32>>, +done: List<&2, U32>, +stack: List<&2, B.Fm>) -> Bool:
  Bool.and(B.calls.in(done, cal, List.append(&2, U32, B.fms.units(stack), done)), frames_ok(stack, cal, List.append(&2, U32, B.fms.units(stack), done)))

def kinv(+cal: List<&2, List<&2, U32>>, s: B.Ds) -> Bool:
  match s:
    case B.Ds{stack, roots, done, order, ers}:
      kinv4(cal, done, stack)

def calls_mono(d: List<&2, U32>, +cal: List<&2, List<&2, U32>>, +x: List<&2, U32>, +y: List<&2, U32>,
    +h: {B.calls.in(d, cal, x) == True{} : Bool}, +s: {B.all.in(x, y) == True{} : Bool}) -> {B.calls.in(d, cal, y) == True{} : Bool}:
  match d:
    case Nil{}:
      {==}
    case Con{+v, +t}:
      and_intro(B.all.in(B.ids.at(cal, v), y), B.calls.in(t, cal, y),
        sub_trans(B.ids.at(cal, v), x, y, MB.eq_true_of_and_left(B.all.in(B.ids.at(cal, v), x), B.calls.in(t, cal, x), h), s),
        calls_mono(t, cal, x, y, MB.eq_true_of_and_right(B.all.in(B.ids.at(cal, v), x), B.calls.in(t, cal, x), h), s))

def app_mono(+x: List<&2, U32>, +y: List<&2, U32>, +r: List<&2, U32>, +s: {B.all.in(x, y) == True{} : Bool}) ->
    {B.all.in(List.append(&2, U32, x, r), List.append(&2, U32, y, r)) == True{} : Bool}:
  sub_app(x, r, List.append(&2, U32, y, r), sub_trans(x, y, List.append(&2, U32, y, r), s, sub_l(y, r)), sub_r(y, r))

def frames_mono(st: List<&2, B.Fm>, +cal: List<&2, List<&2, U32>>, +x: List<&2, U32>, +y: List<&2, U32>,
    +h: {frames_ok(st, cal, x) == True{} : Bool}, +s: {B.all.in(x, y) == True{} : Bool}) -> {frames_ok(st, cal, y) == True{} : Bool}:
  match st:
    case Nil{}:
      {==}
    case Con{f, +t}:
      match f:
        case B.Fm{+u, +rest}:
          and_intro(B.all.in(B.ids.at(cal, u), List.append(&2, U32, y, rest)), frames_ok(t, cal, y),
            sub_trans(B.ids.at(cal, u), List.append(&2, U32, x, rest), List.append(&2, U32, y, rest),
              MB.eq_true_of_and_left(B.all.in(B.ids.at(cal, u), List.append(&2, U32, x, rest)), frames_ok(t, cal, x), h), app_mono(x, y, rest, s)),
            frames_mono(t, cal, x, y, MB.eq_true_of_and_right(B.all.in(B.ids.at(cal, u), List.append(&2, U32, x, rest)), frames_ok(t, cal, x), h), s))

# a call followed, its unit among c already
def follow_sub(+c: List<&2, U32>, +x: U32, +rs: List<&2, U32>, +hc: {B.has(c, x) == True{} : Bool}) ->
    {B.all.in(List.append(&2, U32, c, Con{x, rs}), List.append(&2, U32, c, rs)) == True{} : Bool}:
  sub_app(c, Con{x, rs}, List.append(&2, U32, c, rs), sub_l(c, rs),
    and_intro(B.has(List.append(&2, U32, c, rs), x), B.all.in(rs, List.append(&2, U32, c, rs)), in_l(c, rs, x, hc), sub_r(c, rs)))

# a call followed, its unit pushed
def push_sub(+c: List<&2, U32>, +x: U32, +rs: List<&2, U32>) ->
    {B.all.in(List.append(&2, U32, c, Con{x, rs}), Con{x, List.append(&2, U32, c, rs)}) == True{} : Bool}:
  sub_app(c, Con{x, rs}, Con{x, List.append(&2, U32, c, rs)}, all_in_mono(c, List.append(&2, U32, c, rs), x, sub_l(c, rs)),
    and_intro(B.has(Con{x, List.append(&2, U32, c, rs)}, x), B.all.in(rs, Con{x, List.append(&2, U32, c, rs)}),
      has_self(List.append(&2, U32, c, rs), x), all_in_mono(rs, List.append(&2, U32, c, rs), x, sub_r(c, rs))))

def root_closed(+seen: Bool, +r: U32, +rt: List<&2, U32>, +done: List<&2, U32>, +order: List<&2, U32>, +ers: List<&2, B.Er>, +cal: List<&2, List<&2, U32>>,
    +h: {kinv4(cal, done, Nil{}) == True{} : Bool}) ->
    {kinv(cal, B.ds.root.k(seen, r, rt, done, order, ers, cal)) == True{} : Bool}:
  match seen:
    case True{}:
      h
    case False{}:
      and_intro(B.calls.in(done, cal, Con{r, done}), frames_ok([B.Fm{r, B.ids.at(cal, r)}], cal, Con{r, done}),
        calls_mono(done, cal, done, Con{r, done}, MB.eq_true_of_and_left(B.calls.in(done, cal, done), frames_ok(Nil{}, cal, done), h), sub_cons(done, r)),
        and_intro(B.all.in(B.ids.at(cal, r), List.append(&2, U32, Con{r, done}, B.ids.at(cal, r))), True{}, sub_r(Con{r, done}, B.ids.at(cal, r)), {==}))

def call_closed.k(+seen: Bool, +cyc: Bool, +c: U32, +u: U32, +rs: List<&2, U32>, +st: List<&2, B.Fm>, +roots: List<&2, U32>,
    +done: List<&2, U32>, +order: List<&2, U32>, +ers: List<&2, B.Er>, +cal: List<&2, List<&2, U32>>, +obs: List<&2, B.Ob>, +us: List<&2, B.Un>,
    +e1: {seen == B.has(done, c) : Bool}, +e2: {cyc == B.has(Con{u, B.fms.units(st)}, c) : Bool},
    +hcalls: {B.calls.in(done, cal, Con{u, List.append(&2, U32, B.fms.units(st), done)}) == True{} : Bool},
    +hu: {B.all.in(B.ids.at(cal, u), List.append(&2, U32, Con{u, List.append(&2, U32, B.fms.units(st), done)}, Con{c, rs})) == True{} : Bool},
    +hst: {frames_ok(st, cal, Con{u, List.append(&2, U32, B.fms.units(st), done)}) == True{} : Bool}) ->
    {kinv(cal, B.ds.call.k(seen, cyc, c, u, rs, st, roots, done, order, ers, cal, obs, us)) == True{} : Bool}:
  match seen:
    case True{}:
      and_intro(B.calls.in(done, cal, Con{u, List.append(&2, U32, B.fms.units(st), done)}),
        frames_ok(Con{B.Fm{u, rs}, st}, cal, Con{u, List.append(&2, U32, B.fms.units(st), done)}), hcalls,
        and_intro(B.all.in(B.ids.at(cal, u), List.append(&2, U32, Con{u, List.append(&2, U32, B.fms.units(st), done)}, rs)),
          frames_ok(st, cal, Con{u, List.append(&2, U32, B.fms.units(st), done)}),
          sub_trans(B.ids.at(cal, u), List.append(&2, U32, Con{u, List.append(&2, U32, B.fms.units(st), done)}, Con{c, rs}),
            List.append(&2, U32, Con{u, List.append(&2, U32, B.fms.units(st), done)}, rs), hu,
            follow_sub(Con{u, List.append(&2, U32, B.fms.units(st), done)}, c, rs,
              has_sub(done, Con{u, List.append(&2, U32, B.fms.units(st), done)}, c,
                all_in_mono(done, List.append(&2, U32, B.fms.units(st), done), u, sub_r(B.fms.units(st), done)),
                Equal.sym(Bool, True{}, B.has(done, c), e1)))),
          hst))
    case False{}:
      match cyc:
        case True{}:
          and_intro(B.calls.in(done, cal, Con{u, List.append(&2, U32, B.fms.units(st), done)}),
            frames_ok(Con{B.Fm{u, rs}, st}, cal, Con{u, List.append(&2, U32, B.fms.units(st), done)}), hcalls,
            and_intro(B.all.in(B.ids.at(cal, u), List.append(&2, U32, Con{u, List.append(&2, U32, B.fms.units(st), done)}, rs)),
              frames_ok(st, cal, Con{u, List.append(&2, U32, B.fms.units(st), done)}),
              sub_trans(B.ids.at(cal, u), List.append(&2, U32, Con{u, List.append(&2, U32, B.fms.units(st), done)}, Con{c, rs}),
                List.append(&2, U32, Con{u, List.append(&2, U32, B.fms.units(st), done)}, rs), hu,
                follow_sub(Con{u, List.append(&2, U32, B.fms.units(st), done)}, c, rs,
                  in_l(Con{u, B.fms.units(st)}, done, c, Equal.sym(Bool, True{}, B.has(Con{u, B.fms.units(st)}, c), e2)))),
              hst))
        case False{}:
          and_intro(B.calls.in(done, cal, Con{c, Con{u, List.append(&2, U32, B.fms.units(st), done)}}),
            frames_ok(Con{B.Fm{c, B.ids.at(cal, c)}, Con{B.Fm{u, rs}, st}}, cal, Con{c, Con{u, List.append(&2, U32, B.fms.units(st), done)}}),
            calls_mono(done, cal, Con{u, List.append(&2, U32, B.fms.units(st), done)}, Con{c, Con{u, List.append(&2, U32, B.fms.units(st), done)}}, hcalls,
              sub_cons(Con{u, List.append(&2, U32, B.fms.units(st), done)}, c)),
            and_intro(B.all.in(B.ids.at(cal, c), List.append(&2, U32, Con{c, Con{u, List.append(&2, U32, B.fms.units(st), done)}}, B.ids.at(cal, c))),
              frames_ok(Con{B.Fm{u, rs}, st}, cal, Con{c, Con{u, List.append(&2, U32, B.fms.units(st), done)}}),
              sub_r(Con{c, Con{u, List.append(&2, U32, B.fms.units(st), done)}}, B.ids.at(cal, c)),
              and_intro(B.all.in(B.ids.at(cal, u), List.append(&2, U32, Con{c, Con{u, List.append(&2, U32, B.fms.units(st), done)}}, rs)),
                frames_ok(st, cal, Con{c, Con{u, List.append(&2, U32, B.fms.units(st), done)}}),
                sub_trans(B.ids.at(cal, u), List.append(&2, U32, Con{u, List.append(&2, U32, B.fms.units(st), done)}, Con{c, rs}),
                  Con{c, List.append(&2, U32, Con{u, List.append(&2, U32, B.fms.units(st), done)}, rs)}, hu,
                  push_sub(Con{u, List.append(&2, U32, B.fms.units(st), done)}, c, rs)),
                frames_mono(st, cal, Con{u, List.append(&2, U32, B.fms.units(st), done)}, Con{c, Con{u, List.append(&2, U32, B.fms.units(st), done)}}, hst,
                  sub_cons(Con{u, List.append(&2, U32, B.fms.units(st), done)}, c)))))

def call_closed(+seen: Bool, +cyc: Bool, +c: U32, +u: U32, +rs: List<&2, U32>, +st: List<&2, B.Fm>, +roots: List<&2, U32>,
    +done: List<&2, U32>, +order: List<&2, U32>, +ers: List<&2, B.Er>, +cal: List<&2, List<&2, U32>>, +obs: List<&2, B.Ob>, +us: List<&2, B.Un>,
    +e1: {seen == B.has(done, c) : Bool}, +e2: {cyc == B.has(Con{u, B.fms.units(st)}, c) : Bool},
    +h: {kinv4(cal, done, Con{B.Fm{u, Con{c, rs}}, st}) == True{} : Bool}) ->
    {kinv(cal, B.ds.call.k(seen, cyc, c, u, rs, st, roots, done, order, ers, cal, obs, us)) == True{} : Bool}:
  +cc = {Con{u, List.append(&2, U32, B.fms.units(st), done)} : List<&2, U32>}
  +hcalls = MB.eq_true_of_and_left(B.calls.in(done, cal, cc), frames_ok(Con{B.Fm{u, Con{c, rs}}, st}, cal, cc), h)
  +hfr = MB.eq_true_of_and_right(B.calls.in(done, cal, cc), frames_ok(Con{B.Fm{u, Con{c, rs}}, st}, cal, cc), h)
  +hu = MB.eq_true_of_and_left(B.all.in(B.ids.at(cal, u), List.append(&2, U32, cc, Con{c, rs})), frames_ok(st, cal, cc), hfr)
  +hst = MB.eq_true_of_and_right(B.all.in(B.ids.at(cal, u), List.append(&2, U32, cc, Con{c, rs})), frames_ok(st, cal, cc), hfr)
  call_closed.k(seen, cyc, c, u, rs, st, roots, done, order, ers, cal, obs, us, e1, e2, hcalls, hu, hst)

def done_closed.k(+ok: Bool, +u: U32, +st: List<&2, B.Fm>, +roots: List<&2, U32>, +done: List<&2, U32>, +order: List<&2, U32>,
    +ers: List<&2, B.Er>, +obs: List<&2, B.Ob>, +us: List<&2, B.Un>, +cal: List<&2, List<&2, U32>>,
    +hu: {B.all.in(B.ids.at(cal, u), List.append(&2, U32, B.fms.units(st), Con{u, done})) == True{} : Bool},
    +hd: {B.calls.in(done, cal, List.append(&2, U32, B.fms.units(st), Con{u, done})) == True{} : Bool},
    +hf: {frames_ok(st, cal, List.append(&2, U32, B.fms.units(st), Con{u, done})) == True{} : Bool}) ->
    {kinv(cal, B.ds.done.k(ok, u, st, roots, done, order, ers, obs, us)) == True{} : Bool}:
  match ok:
    case True{}:
      and_intro(B.calls.in(Con{u, done}, cal, List.append(&2, U32, B.fms.units(st), Con{u, done})), frames_ok(st, cal, List.append(&2, U32, B.fms.units(st), Con{u, done})),
        and_intro(B.all.in(B.ids.at(cal, u), List.append(&2, U32, B.fms.units(st), Con{u, done})), B.calls.in(done, cal, List.append(&2, U32, B.fms.units(st), Con{u, done})), hu, hd),
        hf)
    case False{}:
      and_intro(B.calls.in(Con{u, done}, cal, List.append(&2, U32, B.fms.units(st), Con{u, done})), frames_ok(st, cal, List.append(&2, U32, B.fms.units(st), Con{u, done})),
        and_intro(B.all.in(B.ids.at(cal, u), List.append(&2, U32, B.fms.units(st), Con{u, done})), B.calls.in(done, cal, List.append(&2, U32, B.fms.units(st), Con{u, done})), hu, hd),
        hf)

# a unit popped: its callees among c, all followed; c the same units
def done_closed(+ok: Bool, +u: U32, +st: List<&2, B.Fm>, +roots: List<&2, U32>, +done: List<&2, U32>, +order: List<&2, U32>,
    +ers: List<&2, B.Er>, +obs: List<&2, B.Ob>, +us: List<&2, B.Un>, +cal: List<&2, List<&2, U32>>,
    +h: {kinv4(cal, done, Con{B.Fm{u, Nil{}}, st}) == True{} : Bool}) ->
    {kinv(cal, B.ds.done.k(ok, u, st, roots, done, order, ers, obs, us)) == True{} : Bool}:
  +cc = {Con{u, List.append(&2, U32, B.fms.units(st), done)} : List<&2, U32>}
  +cn = List.append(&2, U32, B.fms.units(st), Con{u, done})
  +sb = pop_sub(u, B.fms.units(st), done)
  +hcalls = MB.eq_true_of_and_left(B.calls.in(done, cal, cc), frames_ok(Con{B.Fm{u, Nil{}}, st}, cal, cc), h)
  +hfr = MB.eq_true_of_and_right(B.calls.in(done, cal, cc), frames_ok(Con{B.Fm{u, Nil{}}, st}, cal, cc), h)
  +hu = MB.eq_true_of_and_left(B.all.in(B.ids.at(cal, u), List.append(&2, U32, cc, Nil{})), frames_ok(st, cal, cc), hfr)
  +hst = MB.eq_true_of_and_right(B.all.in(B.ids.at(cal, u), List.append(&2, U32, cc, Nil{})), frames_ok(st, cal, cc), hfr)
  done_closed.k(ok, u, st, roots, done, order, ers, obs, us, cal,
    sub_trans(B.ids.at(cal, u), List.append(&2, U32, cc, Nil{}), cn, hu, sub_app(cc, Nil{}, cn, sb, {==})),
    calls_mono(done, cal, cc, cn, hcalls, sb),
    frames_mono(st, cal, cc, cn, hst, sb))

def step_closed(s: B.Ds, +cal: List<&2, List<&2, U32>>, +obs: List<&2, B.Ob>, +us: List<&2, B.Un>, +h: {kinv(cal, s) == True{} : Bool}) ->
    {kinv(cal, B.ds.step(s, cal, obs, us)) == True{} : Bool}:
  match s:
    case B.Ds{stack, +roots, +done, +order, +ers}:
      match stack:
        case Nil{}:
          match roots:
            case Nil{}:
              h
            case Con{+r, +rt}:
              root_closed(B.has(done, r), r, rt, done, order, ers, cal, h)
        case Con{f, +st}:
          match f:
            case B.Fm{+u, rest}:
              match rest:
                case Nil{}:
                  done_closed(B.all.in(B.ids.at(cal, u), order), u, st, roots, done, order, ers, obs, us, cal, h)
                case Con{+c, +rs}:
                  call_closed(B.has(done, c), B.has(Con{u, B.fms.units(st)}, c), c, u, rs, st, roots, done, order, ers, cal, obs, us, {==}, {==}, h)

def go_closed(n: Nat, +s: B.Ds, +cal: List<&2, List<&2, U32>>, +obs: List<&2, B.Ob>, +us: List<&2, B.Un>, +h: {kinv(cal, s) == True{} : Bool}) ->
    {kinv(cal, B.ds.go(n, s, cal, obs, us)) == True{} : Bool}:
  match n:
    case 0n:
      h
    case 1n+k:
      go_closed(k, B.ds.step(s, cal, obs, us), cal, obs, us, step_closed(s, cal, obs, us, h))

# finished: no stack, so every walked unit's callees walked
def closed_out(s: B.Ds, +cal: List<&2, List<&2, U32>>, +h: {kinv(cal, s) == True{} : Bool}, e: {B.ds.finished(s) == True{} : Bool}) ->
    {B.calls.in(B.ds.walked(s), cal, B.ds.walked(s)) == True{} : Bool}:
  match s:
    case B.Ds{stack, roots, +done, order, ers}:
      match stack:
        case Nil{}:
          match roots:
            case Nil{}:
              MB.eq_true_of_and_left(B.calls.in(done, cal, done), frames_ok(Nil{}, cal, done), h)
            case Con{r, rt}:
              Empty.absurd({B.calls.in(done, cal, done) == True{} : Bool}, MB.false_ne_true()(e))
        case Con{f, st}:
          Empty.absurd({B.calls.in(done, cal, done) == True{} : Bool}, MB.false_ne_true()(e))

def Laws.order.closed(roots, cal, obs, us, h):
  closed_out(B.walk(roots, cal, obs, us), cal,
    go_closed(B.walk.fuel(roots, cal),
      B.Ds{Nil{}, roots, Nil{}, Nil{}, Nil{}}, cal, obs, us, {==}), h)

# The walk ends within its fuel
# -----------------------------
#
# A potential: two turns for each root left; a turn for each frame and
# two for each of its calls left; and two for each call of each unit,
# counted at the unit's position among the calls, while no unit walked
# or on the stack has that position. Each step lowers it by one at least,
# a push freeing its unit's turns, which the frame it pushes takes back
# less one; the fuel is the potential at the start. Counted by position,
# each unit's calls count once, so that the fuel is linear in the calls.

def cost(+b: Bool, +n: Nat) -> Nat:
  match b:
    case True{}:
      0n
    case False{}:
      n

def cost_le(+b: Bool, +n: Nat) -> MNat.le(cost(b, n), n):
  match b:
    case True{}:
      MNat.zero_le(n)
    case False{}:
      MNat.le_refl(n)

def cost_mono(+a: Bool, +b: Bool, +n: Nat) -> MNat.le(cost(Bool.or(a, b), n), cost(b, n)):
  match a:
    case True{}:
      MNat.zero_le(cost(b, n))
    case False{}:
      MNat.le_refl(cost(b, n))

# whether a unit of x has the position i
def taken(x: List<&2, U32>, +i: Nat) -> Bool:
  match x:
    case Nil{}:
      False{}
    case Con{h, t}:
      Bool.or(Nat.is_eq(U32.to_nat(h), i), taken(t, i))

def has_taken(x: List<&2, U32>, +c: U32) -> {B.has(x, c) == taken(x, U32.to_nat(c)) : Bool}:
  match x:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %MU.u32_is_eq_to_nat(h, c) : {Bool.or(U32.is_eq(h, c), B.has(t, c)) == Bool.or(_, taken(t, U32.to_nat(c))) : Bool}
      %has_taken(t, c) : {Bool.or(U32.is_eq(h, c), B.has(t, c)) == Bool.or(U32.is_eq(h, c), _) : Bool}
      {==}

def taken_sub.k(+b: Bool, +a: U32, +t: List<&2, U32>, +y: List<&2, U32>, +j: Nat, +e: {b == Nat.is_eq(U32.to_nat(a), j) : Bool},
    +hs: {B.all.in(Con{a, t}, y) == True{} : Bool}, +h: {Bool.or(b, taken(t, j)) == True{} : Bool},
    ih: {taken(t, j) == True{} : Bool} -> {taken(y, j) == True{} : Bool}) -> {taken(y, j) == True{} : Bool}:
  match b:
    case True{}:
      %MNat.eq_of_is_eq(U32.to_nat(a), j, Equal.sym(Bool, True{}, Nat.is_eq(U32.to_nat(a), j), e)) : {taken(y, _) == True{} : Bool}
      %has_taken(y, a) : {_ == True{} : Bool}
      MB.eq_true_of_and_left(B.has(y, a), B.all.in(t, y), hs)
    case False{}:
      ih(h)

# a position x takes, any list x is among takes
def taken_sub(x: List<&2, U32>, +y: List<&2, U32>, +j: Nat, +hs: {B.all.in(x, y) == True{} : Bool}, +h: {taken(x, j) == True{} : Bool}) ->
    {taken(y, j) == True{} : Bool}:
  match x:
    case Nil{}:
      Empty.absurd({taken(y, j) == True{} : Bool}, MB.false_ne_true()(h))
    case Con{+a, +t}:
      taken_sub.k(Nat.is_eq(U32.to_nat(a), j), a, t, y, j, {==}, hs, h,
        g => taken_sub(t, y, j, MB.eq_true_of_and_right(B.has(y, a), B.all.in(t, y), hs), g))

# the turns of the calls at positions j on not taken by x
def psw(cal: List<&2, List<&2, U32>>, +x: List<&2, U32>, +j: Nat) -> Nat:
  match cal:
    case Nil{}:
      0n
    case Con{h, t}:
      Nat.add(cost(taken(x, j), B.walk.turns(h)), psw(t, x, 1n+j))

def psw_nil(cal: List<&2, List<&2, U32>>, +j: Nat) -> {psw(cal, Nil{}, j) == B.walk.calls(cal) : Nat}:
  match cal:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %psw_nil(t, 1n+j) : {Nat.add(B.walk.turns(h), psw(t, Nil{}, 1n+j)) == Nat.add(B.walk.turns(h), _) : Nat}
      {==}

# more taken, no more turns
def psw_mono(cal: List<&2, List<&2, U32>>, +x: List<&2, U32>, +c: U32, +j: Nat) -> MNat.le(psw(cal, Con{c, x}, j), psw(cal, x, j)):
  match cal:
    case Nil{}:
      MNat.le_refl(0n)
    case Con{+h, +t}:
      MNat.add_le_add(cost(Bool.or(Nat.is_eq(U32.to_nat(c), j), taken(x, j)), B.walk.turns(h)), psw(t, Con{c, x}, 1n+j), cost(taken(x, j), B.walk.turns(h)), psw(t, x, 1n+j),
        cost_mono(Nat.is_eq(U32.to_nat(c), j), taken(x, j), B.walk.turns(h)), psw_mono(t, x, c, 1n+j))

def cost_sub(+x: List<&2, U32>, +y: List<&2, U32>, +j: Nat, +h: {B.all.in(x, y) == True{} : Bool}, +n: Nat, b: Bool, +e: {b == taken(x, j) : Bool}) ->
    MNat.le(cost(taken(y, j), n), cost(b, n)):
  match b:
    case True{}:
      %Equal.sym(Bool, taken(y, j), True{}, taken_sub(x, y, j, h, Equal.sym(Bool, True{}, taken(x, j), e))) : MNat.le(cost(_, n), 0n)
      MNat.le_refl(0n)
    case False{}:
      cost_le(taken(y, j), n)

def psw_sub(cal: List<&2, List<&2, U32>>, +x: List<&2, U32>, +y: List<&2, U32>, +j: Nat, +h: {B.all.in(x, y) == True{} : Bool}) ->
    MNat.le(psw(cal, y, j), psw(cal, x, j)):
  match cal:
    case Nil{}:
      MNat.le_refl(0n)
    case Con{+w, +t}:
      MNat.add_le_add(cost(taken(y, j), B.walk.turns(w)), psw(t, y, 1n+j), cost(taken(x, j), B.walk.turns(w)), psw(t, x, 1n+j),
        cost_sub(x, y, j, h, B.walk.turns(w), taken(x, j), {==}), psw_sub(t, x, y, 1n+j, h))

def succ_add_ne(+k: Nat, j: Nat) -> {Nat.is_eq(1n+Nat.add(k, j), j) == False{} : Bool}:
  match j:
    case 0n:
      {==}
    case 1n+(+i):
      %MNat.add_succ_sym(k, i) : {Nat.is_eq(_, i) == False{} : Bool}
      succ_add_ne(k, i)

def at_self(+c: U32, +j: Nat, +e: {U32.to_nat(c) == j : Nat}) -> {Nat.is_eq(U32.to_nat(c), j) == True{} : Bool}:
  %Equal.sym(Nat, U32.to_nat(c), j, e) : {Nat.is_eq(_, j) == True{} : Bool}
  MNat.is_eq_refl(j)

def at_other(+c: U32, +k: Nat, +j: Nat, +e: {U32.to_nat(c) == 1n+Nat.add(k, j) : Nat}) -> {Nat.is_eq(U32.to_nat(c), j) == False{} : Bool}:
  %Equal.sym(Nat, U32.to_nat(c), 1n+Nat.add(k, j), e) : {Nat.is_eq(_, j) == False{} : Bool}
  succ_add_ne(k, j)

# a unit c at position d + j, which x does not take: taking it frees the
# turns of its calls
def psw_drop(cal: List<&2, List<&2, U32>>, +x: List<&2, U32>, +c: U32, d: Nat, +j: Nat,
    +e: {U32.to_nat(c) == Nat.add(d, j) : Nat}, +hn: {taken(x, Nat.add(d, j)) == False{} : Bool}) ->
    MNat.le(Nat.add(B.walk.turns(B.ids.or(List.get(&2, List<&2, U32>, cal, d))), psw(cal, Con{c, x}, j)), psw(cal, x, j)):
  match cal:
    case Nil{}:
      MNat.le_refl(0n)
    case Con{+h, +t}:
      match d:
        case 0n:
          %Equal.sym(Bool, Nat.is_eq(U32.to_nat(c), j), True{}, at_self(c, j, e)) :
            MNat.le(Nat.add(B.walk.turns(h), Nat.add(cost(Bool.or(_, taken(x, j)), B.walk.turns(h)), psw(t, Con{c, x}, 1n+j))), Nat.add(cost(taken(x, j), B.walk.turns(h)), psw(t, x, 1n+j)))
          %Equal.sym(Bool, taken(x, j), False{}, hn) :
            MNat.le(Nat.add(B.walk.turns(h), psw(t, Con{c, x}, 1n+j)), Nat.add(cost(_, B.walk.turns(h)), psw(t, x, 1n+j)))
          MNat.add_le_add_left(psw(t, Con{c, x}, 1n+j), psw(t, x, 1n+j), B.walk.turns(h), psw_mono(t, x, c, 1n+j))
        case 1n+(+k):
          %Equal.sym(Bool, Nat.is_eq(U32.to_nat(c), j), False{}, at_other(c, k, j, e)) :
            MNat.le(Nat.add(B.walk.turns(B.ids.or(List.get(&2, List<&2, U32>, t, k))), Nat.add(cost(Bool.or(_, taken(x, j)), B.walk.turns(h)), psw(t, Con{c, x}, 1n+j))), Nat.add(cost(taken(x, j), B.walk.turns(h)), psw(t, x, 1n+j)))
          %MNat.add_left_comm(cost(taken(x, j), B.walk.turns(h)), B.walk.turns(B.ids.or(List.get(&2, List<&2, U32>, t, k))), psw(t, Con{c, x}, 1n+j)) :
            MNat.le(_, Nat.add(cost(taken(x, j), B.walk.turns(h)), psw(t, x, 1n+j)))
          MNat.add_le_add_left(Nat.add(B.walk.turns(B.ids.or(List.get(&2, List<&2, U32>, t, k))), psw(t, Con{c, x}, 1n+j)), psw(t, x, 1n+j), cost(taken(x, j), B.walk.turns(h)),
            psw_drop(t, x, c, k, 1n+j,
              Equal.trans(Nat, U32.to_nat(c), 1n+Nat.add(k, j), Nat.add(k, 1n+j), e, MNat.add_succ_sym(k, j)),
              ME.subst(Nat, z => {taken(x, z) == False{} : Bool}, 1n+Nat.add(k, j), Nat.add(k, 1n+j), MNat.add_succ_sym(k, j), hn)))

def untaken(+x: List<&2, U32>, +c: U32, +h: {B.has(x, c) == False{} : Bool}) -> {taken(x, Nat.add(U32.to_nat(c), 0n)) == False{} : Bool}:
  %MNat.add_zero_sym(U32.to_nat(c)) : {taken(x, _) == False{} : Bool}
  %has_taken(x, c) : {_ == False{} : Bool}
  h

# a unit neither walked nor on the stack, pushed: its calls' turns freed
def drop_at(+cal: List<&2, List<&2, U32>>, +x: List<&2, U32>, +c: U32, +h: {B.has(x, c) == False{} : Bool}) ->
    MNat.le(Nat.add(B.walk.turns(B.ids.at(cal, c)), psw(cal, Con{c, x}, 0n)), psw(cal, x, 0n)):
  psw_drop(cal, x, c, U32.to_nat(c), 0n, MNat.add_zero_sym(U32.to_nat(c)), untaken(x, c, h))

# a turn for each frame and two for each of its calls left
def frs(st: List<&2, B.Fm>) -> Nat:
  match st:
    case Nil{}:
      0n
    case Con{f, t}:
      match f:
        case B.Fm{+u, rest}:
          1n+Nat.add(B.walk.turns(rest), frs(t))

def pot(+cal: List<&2, List<&2, U32>>, s: B.Ds) -> Nat:
  match s:
    case B.Ds{+stack, roots, done, order, ers}:
      Nat.add(B.walk.turns(roots), Nat.add(frs(stack), psw(cal, List.append(&2, U32, B.fms.units(stack), done), 0n)))

# The arithmetic of each step's descent

def ar_succ(+l: Nat, +y: Nat) -> MNat.le(1n+Nat.add(l, y), Nat.add(l, 1n+y)):
  %MNat.add_succ(l, y) : MNat.le(_, Nat.add(l, 1n+y))
  MNat.le_refl(Nat.add(l, 1n+y))

def ar_root(+t: Nat, +g: Nat, +s1: Nat, +s: Nat, +h: MNat.le(Nat.add(g, s1), s)) ->
    MNat.le(1n+Nat.add(t, 1n+Nat.add(Nat.add(g, 0n), s1)), 1n+1n+Nat.add(t, s)):
  %MNat.add_zero_sym(g) : MNat.le(1n+Nat.add(t, 1n+Nat.add(_, s1)), 1n+1n+Nat.add(t, s))
  %MNat.add_succ_sym(t, Nat.add(g, s1)) : MNat.le(1n+_, 1n+1n+Nat.add(t, s))
  MNat.succ_le_succ(1n+Nat.add(t, Nat.add(g, s1)), 1n+Nat.add(t, s),
    MNat.succ_le_succ(Nat.add(t, Nat.add(g, s1)), Nat.add(t, s), MNat.add_le_add_left(Nat.add(g, s1), s, t, h)))

def ar_seen(+l: Nat, +y: Nat) -> MNat.le(1n+Nat.add(l, 1n+y), Nat.add(l, 1n+1n+1n+y)):
  MNat.le_trans(1n+Nat.add(l, 1n+y), Nat.add(l, 1n+1n+y), Nat.add(l, 1n+1n+1n+y),
    ar_succ(l, 1n+y), MNat.add_le_add_left(1n+1n+y, 1n+1n+1n+y, l, MNat.le_succ(1n+1n+y)))

def ar_push.k(+g: Nat, +k: Nat, +s1: Nat, +s: Nat, +h: MNat.le(Nat.add(g, s1), s)) -> MNat.le(Nat.add(Nat.add(g, 1n+k), s1), 1n+Nat.add(k, s)):
  %MNat.add_succ_sym(g, k) : MNat.le(Nat.add(_, s1), 1n+Nat.add(k, s))
  %MNat.add_assoc_sym(g, k, s1) : MNat.le(1n+_, 1n+Nat.add(k, s))
  %MNat.add_left_comm(k, g, s1) : MNat.le(1n+_, 1n+Nat.add(k, s))
  MNat.succ_le_succ(Nat.add(k, Nat.add(g, s1)), Nat.add(k, s), MNat.add_le_add_left(Nat.add(g, s1), s, k, h))

def ar_push(+l: Nat, +g: Nat, +k: Nat, +s1: Nat, +s: Nat, +h: MNat.le(Nat.add(g, s1), s)) ->
    MNat.le(1n+Nat.add(l, 1n+Nat.add(Nat.add(g, 1n+k), s1)), Nat.add(l, 1n+1n+1n+Nat.add(k, s))):
  MNat.le_trans(1n+Nat.add(l, 1n+Nat.add(Nat.add(g, 1n+k), s1)), Nat.add(l, 1n+1n+Nat.add(Nat.add(g, 1n+k), s1)), Nat.add(l, 1n+1n+1n+Nat.add(k, s)),
    ar_succ(l, 1n+Nat.add(Nat.add(g, 1n+k), s1)),
    MNat.add_le_add_left(1n+1n+Nat.add(Nat.add(g, 1n+k), s1), 1n+1n+1n+Nat.add(k, s), l,
      MNat.succ_le_succ(1n+Nat.add(Nat.add(g, 1n+k), s1), 1n+1n+Nat.add(k, s),
        MNat.succ_le_succ(Nat.add(Nat.add(g, 1n+k), s1), 1n+Nat.add(k, s), ar_push.k(g, k, s1, s, h)))))

def has_app(p: List<&2, U32>, +q: List<&2, U32>, +x: U32) -> {Bool.or(B.has(p, x), B.has(q, x)) == B.has(List.append(&2, U32, p, q), x) : Bool}:
  match p:
    case Nil{}:
      {==}
    case Con{+a, +t}:
      %has_app(t, q, x) : {Bool.or(Bool.or(U32.is_eq(a, x), B.has(t, x)), B.has(q, x)) == Bool.or(U32.is_eq(a, x), _) : Bool}
      MB.or_assoc(U32.is_eq(a, x), B.has(t, x), B.has(q, x))

def not_in_app(+p: List<&2, U32>, +q: List<&2, U32>, +x: U32, +hp: {B.has(p, x) == False{} : Bool}, +hq: {B.has(q, x) == False{} : Bool}) ->
    {B.has(List.append(&2, U32, p, q), x) == False{} : Bool}:
  %has_app(p, q, x) : {_ == False{} : Bool}
  %Equal.sym(Bool, B.has(p, x), False{}, hp) : {Bool.or(_, B.has(q, x)) == False{} : Bool}
  hq

# Each step lowers the potential

def root_desc(+seen: Bool, +r: U32, +rt: List<&2, U32>, +done: List<&2, U32>, +order: List<&2, U32>, +ers: List<&2, B.Er>,
    +cal: List<&2, List<&2, U32>>, +e: {seen == B.has(done, r) : Bool}) ->
    MNat.le(1n+pot(cal, B.ds.root.k(seen, r, rt, done, order, ers, cal)), pot(cal, B.Ds{Nil{}, Con{r, rt}, done, order, ers})):
  match seen:
    case True{}:
      MNat.le_succ(1n+Nat.add(B.walk.turns(rt), psw(cal, done, 0n)))
    case False{}:
      ar_root(B.walk.turns(rt), B.walk.turns(B.ids.at(cal, r)), psw(cal, Con{r, done}, 0n), psw(cal, done, 0n),
        drop_at(cal, done, r, Equal.sym(Bool, False{}, B.has(done, r), e)))

def call_desc(+seen: Bool, +cyc: Bool, +c: U32, +u: U32, +rs: List<&2, U32>, +st: List<&2, B.Fm>, +roots: List<&2, U32>,
    +done: List<&2, U32>, +order: List<&2, U32>, +ers: List<&2, B.Er>, +cal: List<&2, List<&2, U32>>, +obs: List<&2, B.Ob>, +us: List<&2, B.Un>,
    +e1: {seen == B.has(done, c) : Bool}, +e2: {cyc == B.has(Con{u, B.fms.units(st)}, c) : Bool}) ->
    MNat.le(1n+pot(cal, B.ds.call.k(seen, cyc, c, u, rs, st, roots, done, order, ers, cal, obs, us)), pot(cal, B.Ds{Con{B.Fm{u, Con{c, rs}}, st}, roots, done, order, ers})):
  match seen:
    case True{}:
      ar_seen(B.walk.turns(roots), Nat.add(Nat.add(B.walk.turns(rs), frs(st)), psw(cal, Con{u, List.append(&2, U32, B.fms.units(st), done)}, 0n)))
    case False{}:
      match cyc:
        case True{}:
          ar_seen(B.walk.turns(roots), Nat.add(Nat.add(B.walk.turns(rs), frs(st)), psw(cal, Con{u, List.append(&2, U32, B.fms.units(st), done)}, 0n)))
        case False{}:
          ar_push(B.walk.turns(roots), B.walk.turns(B.ids.at(cal, c)), Nat.add(B.walk.turns(rs), frs(st)), psw(cal, Con{c, Con{u, List.append(&2, U32, B.fms.units(st), done)}}, 0n), psw(cal, Con{u, List.append(&2, U32, B.fms.units(st), done)}, 0n),
            drop_at(cal, Con{u, List.append(&2, U32, B.fms.units(st), done)}, c,
              not_in_app(Con{u, B.fms.units(st)}, done, c, Equal.sym(Bool, False{}, B.has(Con{u, B.fms.units(st)}, c), e2),
                Equal.sym(Bool, False{}, B.has(done, c), e1))))

def pop_desc(+u: U32, +st: List<&2, B.Fm>, +roots: List<&2, U32>, +done: List<&2, U32>, +cal: List<&2, List<&2, U32>>) ->
    MNat.le(1n+Nat.add(B.walk.turns(roots), Nat.add(frs(st), psw(cal, List.append(&2, U32, B.fms.units(st), Con{u, done}), 0n))), Nat.add(B.walk.turns(roots), 1n+Nat.add(frs(st), psw(cal, Con{u, List.append(&2, U32, B.fms.units(st), done)}, 0n)))):
  MNat.le_trans(1n+Nat.add(B.walk.turns(roots), Nat.add(frs(st), psw(cal, List.append(&2, U32, B.fms.units(st), Con{u, done}), 0n))), Nat.add(B.walk.turns(roots), 1n+Nat.add(frs(st), psw(cal, List.append(&2, U32, B.fms.units(st), Con{u, done}), 0n))), Nat.add(B.walk.turns(roots), 1n+Nat.add(frs(st), psw(cal, Con{u, List.append(&2, U32, B.fms.units(st), done)}, 0n))),
    ar_succ(B.walk.turns(roots), Nat.add(frs(st), psw(cal, List.append(&2, U32, B.fms.units(st), Con{u, done}), 0n))),
    MNat.add_le_add_left(1n+Nat.add(frs(st), psw(cal, List.append(&2, U32, B.fms.units(st), Con{u, done}), 0n)), 1n+Nat.add(frs(st), psw(cal, Con{u, List.append(&2, U32, B.fms.units(st), done)}, 0n)), B.walk.turns(roots),
      MNat.succ_le_succ(Nat.add(frs(st), psw(cal, List.append(&2, U32, B.fms.units(st), Con{u, done}), 0n)), Nat.add(frs(st), psw(cal, Con{u, List.append(&2, U32, B.fms.units(st), done)}, 0n)),
        MNat.add_le_add_left(psw(cal, List.append(&2, U32, B.fms.units(st), Con{u, done}), 0n), psw(cal, Con{u, List.append(&2, U32, B.fms.units(st), done)}, 0n), frs(st), psw_sub(cal, Con{u, List.append(&2, U32, B.fms.units(st), done)}, List.append(&2, U32, B.fms.units(st), Con{u, done}), 0n, pop_sub(u, B.fms.units(st), done))))))

def done_desc(+ok: Bool, +u: U32, +st: List<&2, B.Fm>, +roots: List<&2, U32>, +done: List<&2, U32>, +order: List<&2, U32>,
    +ers: List<&2, B.Er>, +obs: List<&2, B.Ob>, +us: List<&2, B.Un>, +cal: List<&2, List<&2, U32>>) ->
    MNat.le(1n+pot(cal, B.ds.done.k(ok, u, st, roots, done, order, ers, obs, us)), pot(cal, B.Ds{Con{B.Fm{u, Nil{}}, st}, roots, done, order, ers})):
  match ok:
    case True{}:
      pop_desc(u, st, roots, done, cal)
    case False{}:
      pop_desc(u, st, roots, done, cal)

def step_desc(s: B.Ds, +cal: List<&2, List<&2, U32>>, +obs: List<&2, B.Ob>, +us: List<&2, B.Un>, +nf: {B.ds.finished(s) == False{} : Bool}) ->
    MNat.le(1n+pot(cal, B.ds.step(s, cal, obs, us)), pot(cal, s)):
  match s:
    case B.Ds{stack, +roots, +done, +order, +ers}:
      match stack:
        case Nil{}:
          match roots:
            case Nil{}:
              Empty.absurd(MNat.le(1n+pot(cal, B.Ds{Nil{}, Nil{}, done, order, ers}), pot(cal, B.Ds{Nil{}, Nil{}, done, order, ers})),
                MB.true_ne_false()(nf))
            case Con{+r, +rt}:
              root_desc(B.has(done, r), r, rt, done, order, ers, cal, {==})
        case Con{f, +st}:
          match f:
            case B.Fm{+u, rest}:
              match rest:
                case Nil{}:
                  done_desc(B.all.in(B.ids.at(cal, u), order), u, st, roots, done, order, ers, obs, us, cal)
                case Con{+c, +rs}:
                  call_desc(B.has(done, c), B.has(Con{u, B.fms.units(st)}, c), c, u, rs, st, roots, done, order, ers, cal, obs, us, {==}, {==})

# a finished walk stays finished
def step_fin(s: B.Ds, +cal: List<&2, List<&2, U32>>, +obs: List<&2, B.Ob>, +us: List<&2, B.Un>, +h: {B.ds.finished(s) == True{} : Bool}) ->
    {B.ds.finished(B.ds.step(s, cal, obs, us)) == True{} : Bool}:
  match s:
    case B.Ds{stack, roots, done, order, ers}:
      match stack:
        case Nil{}:
          match roots:
            case Nil{}:
              {==}
            case Con{r, rt}:
              Empty.absurd({B.ds.finished(B.ds.step(B.Ds{Nil{}, Con{r, rt}, done, order, ers}, cal, obs, us)) == True{} : Bool}, MB.false_ne_true()(h))
        case Con{f, st}:
          Empty.absurd({B.ds.finished(B.ds.step(B.Ds{Con{f, st}, roots, done, order, ers}, cal, obs, us)) == True{} : Bool}, MB.false_ne_true()(h))

def go_fin(n: Nat, +s: B.Ds, +cal: List<&2, List<&2, U32>>, +obs: List<&2, B.Ob>, +us: List<&2, B.Un>, +h: {B.ds.finished(s) == True{} : Bool}) ->
    {B.ds.finished(B.ds.go(n, s, cal, obs, us)) == True{} : Bool}:
  match n:
    case 0n:
      h
    case 1n+k:
      go_fin(k, B.ds.step(s, cal, obs, us), cal, obs, us, step_fin(s, cal, obs, us, h))

# a walk unfinished at the bound 0: its potential is not 0
def pot_pos(s: B.Ds, +cal: List<&2, List<&2, U32>>, +hf: MNat.le(pot(cal, s), 0n)) -> {B.ds.finished(s) == True{} : Bool}:
  match s:
    case B.Ds{stack, roots, done, order, ers}:
      match stack:
        case Nil{}:
          match roots:
            case Nil{}:
              {==}
            case Con{r, rt}:
              Empty.absurd({B.ds.finished(B.Ds{Nil{}, Con{r, rt}, done, order, ers}) == True{} : Bool}, MB.false_ne_true()(hf))
        case Con{f, st}:
          match f:
            case B.Fm{u, rest}:
              Empty.absurd({B.ds.finished(B.Ds{Con{B.Fm{u, rest}, st}, roots, done, order, ers}) == True{} : Bool},
                MB.false_ne_true()(ME.subst(Nat, z => MNat.le(z, 0n),
                  Nat.add(B.walk.turns(roots), 1n+Nat.add(Nat.add(B.walk.turns(rest), frs(st)), psw(cal, Con{u, List.append(&2, U32, B.fms.units(st), done)}, 0n))),
                  1n+Nat.add(B.walk.turns(roots), Nat.add(Nat.add(B.walk.turns(rest), frs(st)), psw(cal, Con{u, List.append(&2, U32, B.fms.units(st), done)}, 0n))),
                  MNat.add_succ(B.walk.turns(roots), Nat.add(Nat.add(B.walk.turns(rest), frs(st)), psw(cal, Con{u, List.append(&2, U32, B.fms.units(st), done)}, 0n))), hf)))

def ends_k(+fin: Bool, +s: B.Ds, +cal: List<&2, List<&2, U32>>, +obs: List<&2, B.Ob>, +us: List<&2, B.Un>, +k: Nat,
    +e: {fin == B.ds.finished(s) : Bool}, +hf: MNat.le(pot(cal, s), 1n+k),
    ih: MNat.le(pot(cal, B.ds.step(s, cal, obs, us)), k) -> {B.ds.finished(B.ds.go(k, B.ds.step(s, cal, obs, us), cal, obs, us)) == True{} : Bool}) ->
    {B.ds.finished(B.ds.go(k, B.ds.step(s, cal, obs, us), cal, obs, us)) == True{} : Bool}:
  match fin:
    case True{}:
      go_fin(k, B.ds.step(s, cal, obs, us), cal, obs, us, step_fin(s, cal, obs, us, Equal.sym(Bool, True{}, B.ds.finished(s), e)))
    case False{}:
      ih(MNat.le_of_succ_le_succ(pot(cal, B.ds.step(s, cal, obs, us)), k,
        MNat.le_trans(1n+pot(cal, B.ds.step(s, cal, obs, us)), pot(cal, s), 1n+k,
          step_desc(s, cal, obs, us, Equal.sym(Bool, False{}, B.ds.finished(s), e)), hf)))

# within fuel no less than its potential, the walk finishes
def ends(n: Nat, +s: B.Ds, +cal: List<&2, List<&2, U32>>, +obs: List<&2, B.Ob>, +us: List<&2, B.Un>, +hf: MNat.le(pot(cal, s), n)) ->
    {B.ds.finished(B.ds.go(n, s, cal, obs, us)) == True{} : Bool}:
  match n:
    case 0n:
      pot_pos(s, cal, hf)
    case 1n+(+k):
      ends_k(B.ds.finished(s), s, cal, obs, us, k, {==}, hf, q => ends(k, B.ds.step(s, cal, obs, us), cal, obs, us, q))

# the fuel is the potential at the start
def fuel_pot(+roots: List<&2, U32>, +cal: List<&2, List<&2, U32>>) -> MNat.le(pot(cal, B.Ds{Nil{}, roots, Nil{}, Nil{}, Nil{}}), B.walk.fuel(roots, cal)):
  %Equal.sym(Nat, psw(cal, Nil{}, 0n), B.walk.calls(cal), psw_nil(cal, 0n)) : MNat.le(Nat.add(B.walk.turns(roots), _), B.walk.fuel(roots, cal))
  MNat.le_refl(B.walk.fuel(roots, cal))

def walk_ends(+roots: List<&2, U32>, +cal: List<&2, List<&2, U32>>, +obs: List<&2, B.Ob>, +us: List<&2, B.Un>) ->
    {B.ds.finished(B.walk(roots, cal, obs, us)) == True{} : Bool}:
  ends(B.walk.fuel(roots, cal), B.Ds{Nil{}, roots, Nil{}, Nil{}, Nil{}}, cal, obs, us, fuel_pot(roots, cal))

def Laws.order.ends(roots, cal, obs, us):
  walk_ends(roots, cal, obs, us)

# The walk the tool runs
# ----------------------
#
# The fast walk (`walk.fast`) is the walk above with each set its lists
# make kept beside them: lifted, a state gains those sets (`lift`), and
# from a lifted state a step of the fast walk is the lifted step of the
# walk, whatever the state, so that walking the lifted start is lifting
# the walk. The sets are tries on the units' bits: a word put is found
# where it equals the word asked for (`has_put`), whatever was there.

# an empty trie holds no word
def has_none(n: Nat, c: Word(n)) -> {B.wt.has(n, c, B.WtNone{}) == False{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match c:
        case WCon{b, r}:
          match b:
            case True{}:
              {==}
            case False{}:
              {==}

# words equal: their tails, and their last bits
def fin_eq(+a: Bool, +b: Bool, k: Cmp) -> {Bool.and(Cmp.is_eq(k), Cmp.is_eq(Bool.cmp(a, b))) == Cmp.is_eq(Word.cmp.fin(a, b, k)) : Bool}:
  match k:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

def has_put.k(a: Bool, b: Bool, +p: Nat, +xr: Word(p), +cr: Word(p), t: B.Wt,
    ih: @s:B.Wt -> {B.wt.has(p, cr, B.wt.put(p, xr, s)) == Bool.or(Cmp.is_eq(Word.cmp(p, xr, cr)), B.wt.has(p, cr, s)) : Bool}) ->
    {B.wt.has(1n+p, WCon{b, cr}, B.wt.put(1n+p, WCon{a, xr}, t)) ==
      Bool.or(Bool.and(Cmp.is_eq(Word.cmp(p, xr, cr)), Cmp.is_eq(Bool.cmp(a, b))), B.wt.has(1n+p, WCon{b, cr}, t)) : Bool}:
  match a b:
    case True{} True{}:
      match t:
        case B.WtNode{f, tt}:
          %Equal.sym(Bool, Bool.and(Cmp.is_eq(Word.cmp(p, xr, cr)), True{}), Cmp.is_eq(Word.cmp(p, xr, cr)), MB.and_true(Cmp.is_eq(Word.cmp(p, xr, cr)))) :
            {B.wt.has(1n+p, WCon{True{}, cr}, B.wt.put(1n+p, WCon{True{}, xr}, B.WtNode{f, tt})) == Bool.or(_, B.wt.has(1n+p, WCon{True{}, cr}, B.WtNode{f, tt})) : Bool}
          ih(tt)
        case B.WtNone{}:
          %Equal.sym(Bool, Bool.and(Cmp.is_eq(Word.cmp(p, xr, cr)), True{}), Cmp.is_eq(Word.cmp(p, xr, cr)), MB.and_true(Cmp.is_eq(Word.cmp(p, xr, cr)))) :
            {B.wt.has(1n+p, WCon{True{}, cr}, B.wt.put(1n+p, WCon{True{}, xr}, B.WtNone{})) == Bool.or(_, B.wt.has(1n+p, WCon{True{}, cr}, B.WtNone{})) : Bool}
          %has_none(p, cr) : {B.wt.has(p, cr, B.wt.put(p, xr, B.WtNone{})) == Bool.or(Cmp.is_eq(Word.cmp(p, xr, cr)), _) : Bool}
          ih(B.WtNone{})
        case B.WtLeaf{}:
          %Equal.sym(Bool, Bool.and(Cmp.is_eq(Word.cmp(p, xr, cr)), True{}), Cmp.is_eq(Word.cmp(p, xr, cr)), MB.and_true(Cmp.is_eq(Word.cmp(p, xr, cr)))) :
            {B.wt.has(1n+p, WCon{True{}, cr}, B.wt.put(1n+p, WCon{True{}, xr}, B.WtLeaf{})) == Bool.or(_, B.wt.has(1n+p, WCon{True{}, cr}, B.WtLeaf{})) : Bool}
          %has_none(p, cr) : {B.wt.has(p, cr, B.wt.put(p, xr, B.WtNone{})) == Bool.or(Cmp.is_eq(Word.cmp(p, xr, cr)), _) : Bool}
          ih(B.WtNone{})
    case True{} False{}:
      match t:
        case B.WtNode{f, tt}:
          %Equal.sym(Bool, Bool.and(Cmp.is_eq(Word.cmp(p, xr, cr)), False{}), False{}, MB.and_false(Cmp.is_eq(Word.cmp(p, xr, cr)))) :
            {B.wt.has(1n+p, WCon{False{}, cr}, B.wt.put(1n+p, WCon{True{}, xr}, B.WtNode{f, tt})) == Bool.or(_, B.wt.has(1n+p, WCon{False{}, cr}, B.WtNode{f, tt})) : Bool}
          {==}
        case B.WtNone{}:
          %Equal.sym(Bool, Bool.and(Cmp.is_eq(Word.cmp(p, xr, cr)), False{}), False{}, MB.and_false(Cmp.is_eq(Word.cmp(p, xr, cr)))) :
            {B.wt.has(1n+p, WCon{False{}, cr}, B.wt.put(1n+p, WCon{True{}, xr}, B.WtNone{})) == Bool.or(_, B.wt.has(1n+p, WCon{False{}, cr}, B.WtNone{})) : Bool}
          has_none(p, cr)
        case B.WtLeaf{}:
          %Equal.sym(Bool, Bool.and(Cmp.is_eq(Word.cmp(p, xr, cr)), False{}), False{}, MB.and_false(Cmp.is_eq(Word.cmp(p, xr, cr)))) :
            {B.wt.has(1n+p, WCon{False{}, cr}, B.wt.put(1n+p, WCon{True{}, xr}, B.WtLeaf{})) == Bool.or(_, B.wt.has(1n+p, WCon{False{}, cr}, B.WtLeaf{})) : Bool}
          has_none(p, cr)
    case False{} True{}:
      match t:
        case B.WtNode{f, tt}:
          %Equal.sym(Bool, Bool.and(Cmp.is_eq(Word.cmp(p, xr, cr)), False{}), False{}, MB.and_false(Cmp.is_eq(Word.cmp(p, xr, cr)))) :
            {B.wt.has(1n+p, WCon{True{}, cr}, B.wt.put(1n+p, WCon{False{}, xr}, B.WtNode{f, tt})) == Bool.or(_, B.wt.has(1n+p, WCon{True{}, cr}, B.WtNode{f, tt})) : Bool}
          {==}
        case B.WtNone{}:
          %Equal.sym(Bool, Bool.and(Cmp.is_eq(Word.cmp(p, xr, cr)), False{}), False{}, MB.and_false(Cmp.is_eq(Word.cmp(p, xr, cr)))) :
            {B.wt.has(1n+p, WCon{True{}, cr}, B.wt.put(1n+p, WCon{False{}, xr}, B.WtNone{})) == Bool.or(_, B.wt.has(1n+p, WCon{True{}, cr}, B.WtNone{})) : Bool}
          has_none(p, cr)
        case B.WtLeaf{}:
          %Equal.sym(Bool, Bool.and(Cmp.is_eq(Word.cmp(p, xr, cr)), False{}), False{}, MB.and_false(Cmp.is_eq(Word.cmp(p, xr, cr)))) :
            {B.wt.has(1n+p, WCon{True{}, cr}, B.wt.put(1n+p, WCon{False{}, xr}, B.WtLeaf{})) == Bool.or(_, B.wt.has(1n+p, WCon{True{}, cr}, B.WtLeaf{})) : Bool}
          has_none(p, cr)
    case False{} False{}:
      match t:
        case B.WtNode{f, tt}:
          %Equal.sym(Bool, Bool.and(Cmp.is_eq(Word.cmp(p, xr, cr)), True{}), Cmp.is_eq(Word.cmp(p, xr, cr)), MB.and_true(Cmp.is_eq(Word.cmp(p, xr, cr)))) :
            {B.wt.has(1n+p, WCon{False{}, cr}, B.wt.put(1n+p, WCon{False{}, xr}, B.WtNode{f, tt})) == Bool.or(_, B.wt.has(1n+p, WCon{False{}, cr}, B.WtNode{f, tt})) : Bool}
          ih(f)
        case B.WtNone{}:
          %Equal.sym(Bool, Bool.and(Cmp.is_eq(Word.cmp(p, xr, cr)), True{}), Cmp.is_eq(Word.cmp(p, xr, cr)), MB.and_true(Cmp.is_eq(Word.cmp(p, xr, cr)))) :
            {B.wt.has(1n+p, WCon{False{}, cr}, B.wt.put(1n+p, WCon{False{}, xr}, B.WtNone{})) == Bool.or(_, B.wt.has(1n+p, WCon{False{}, cr}, B.WtNone{})) : Bool}
          %has_none(p, cr) : {B.wt.has(p, cr, B.wt.put(p, xr, B.WtNone{})) == Bool.or(Cmp.is_eq(Word.cmp(p, xr, cr)), _) : Bool}
          ih(B.WtNone{})
        case B.WtLeaf{}:
          %Equal.sym(Bool, Bool.and(Cmp.is_eq(Word.cmp(p, xr, cr)), True{}), Cmp.is_eq(Word.cmp(p, xr, cr)), MB.and_true(Cmp.is_eq(Word.cmp(p, xr, cr)))) :
            {B.wt.has(1n+p, WCon{False{}, cr}, B.wt.put(1n+p, WCon{False{}, xr}, B.WtLeaf{})) == Bool.or(_, B.wt.has(1n+p, WCon{False{}, cr}, B.WtLeaf{})) : Bool}
          %has_none(p, cr) : {B.wt.has(p, cr, B.wt.put(p, xr, B.WtNone{})) == Bool.or(Cmp.is_eq(Word.cmp(p, xr, cr)), _) : Bool}
          ih(B.WtNone{})

# a word put, then one asked for: found where they are equal, or where it
# was found before
def has_put(n: Nat, x: Word(n), c: Word(n), t: B.Wt) ->
    {B.wt.has(n, c, B.wt.put(n, x, t)) == Bool.or(Cmp.is_eq(Word.cmp(n, x, c)), B.wt.has(n, c, t)) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+(+p):
      match x:
        case WCon{+a, +xr}:
          match c:
            case WCon{+b, +cr}:
              %fin_eq(a, b, Word.cmp(p, xr, cr)) :
                {B.wt.has(1n+p, WCon{b, cr}, B.wt.put(1n+p, WCon{a, xr}, t)) == Bool.or(_, B.wt.has(1n+p, WCon{b, cr}, t)) : Bool}
              has_put.k(a, b, p, xr, cr, t, s => has_put(p, xr, cr, s))

def vs_put(+t: B.Wt, x: U32, c: U32) -> {B.vs.has(B.vs.put(t, x), c) == Bool.or(U32.is_eq(x, c), B.vs.has(t, c)) : Bool}:
  match x c:
    case U32{xw} U32{cw}:
      has_put(32n, xw, cw, t)

# the set a list makes holds what the list has
def vs_of(xs: List<&2, U32>, +c: U32) -> {B.vs.has(B.vs.of(xs), c) == B.has(xs, c) : Bool}:
  match xs:
    case Nil{}:
      match c:
        case U32{w}:
          has_none(32n, w)
    case Con{+x, +t}:
      %Equal.sym(Bool, B.vs.has(B.vs.put(B.vs.of(t), x), c), Bool.or(U32.is_eq(x, c), B.vs.has(B.vs.of(t), c)), vs_put(B.vs.of(t), x, c)) :
        {_ == Bool.or(U32.is_eq(x, c), B.has(t, c)) : Bool}
      %vs_of(t, c) : {Bool.or(U32.is_eq(x, c), B.vs.has(B.vs.of(t), c)) == Bool.or(U32.is_eq(x, c), _) : Bool}
      {==}

def vs_all(xs: List<&2, U32>, +ys: List<&2, U32>) -> {B.vs.all(xs, B.vs.of(ys)) == B.all.in(xs, ys) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      %vs_of(ys, x) : {Bool.and(B.vs.has(B.vs.of(ys), x), B.vs.all(r, B.vs.of(ys))) == Bool.and(_, B.all.in(r, ys)) : Bool}
      %vs_all(r, ys) : {Bool.and(B.vs.has(B.vs.of(ys), x), B.vs.all(r, B.vs.of(ys))) == Bool.and(B.vs.has(B.vs.of(ys), x), _) : Bool}
      {==}

# words put in either order make one trie: its shape is its set's
def put_comm.k(a: Bool, b: Bool, +p: Nat, +xr: Word(p), +yr: Word(p), t: B.Wt,
    ih: @s:B.Wt -> {B.wt.put(p, xr, B.wt.put(p, yr, s)) == B.wt.put(p, yr, B.wt.put(p, xr, s)) : B.Wt}) ->
    {B.wt.put(1n+p, WCon{a, xr}, B.wt.put(1n+p, WCon{b, yr}, t)) == B.wt.put(1n+p, WCon{b, yr}, B.wt.put(1n+p, WCon{a, xr}, t)) : B.Wt}:
  match a b:
    case True{} True{}:
      match t:
        case B.WtNode{+f, tt}:
          Equal.cong(B.Wt, B.Wt, z => B.WtNode{f, z}, B.wt.put(p, xr, B.wt.put(p, yr, tt)), B.wt.put(p, yr, B.wt.put(p, xr, tt)), ih(tt))
        case B.WtNone{}:
          Equal.cong(B.Wt, B.Wt, z => B.WtNode{B.WtNone{}, z}, B.wt.put(p, xr, B.wt.put(p, yr, B.WtNone{})), B.wt.put(p, yr, B.wt.put(p, xr, B.WtNone{})), ih(B.WtNone{}))
        case B.WtLeaf{}:
          Equal.cong(B.Wt, B.Wt, z => B.WtNode{B.WtNone{}, z}, B.wt.put(p, xr, B.wt.put(p, yr, B.WtNone{})), B.wt.put(p, yr, B.wt.put(p, xr, B.WtNone{})), ih(B.WtNone{}))
    case True{} False{}:
      match t:
        case B.WtNode{f, tt}:
          {==}
        case B.WtNone{}:
          {==}
        case B.WtLeaf{}:
          {==}
    case False{} True{}:
      match t:
        case B.WtNode{f, tt}:
          {==}
        case B.WtNone{}:
          {==}
        case B.WtLeaf{}:
          {==}
    case False{} False{}:
      match t:
        case B.WtNode{f, +tt}:
          Equal.cong(B.Wt, B.Wt, z => B.WtNode{z, tt}, B.wt.put(p, xr, B.wt.put(p, yr, f)), B.wt.put(p, yr, B.wt.put(p, xr, f)), ih(f))
        case B.WtNone{}:
          Equal.cong(B.Wt, B.Wt, z => B.WtNode{z, B.WtNone{}}, B.wt.put(p, xr, B.wt.put(p, yr, B.WtNone{})), B.wt.put(p, yr, B.wt.put(p, xr, B.WtNone{})), ih(B.WtNone{}))
        case B.WtLeaf{}:
          Equal.cong(B.Wt, B.Wt, z => B.WtNode{z, B.WtNone{}}, B.wt.put(p, xr, B.wt.put(p, yr, B.WtNone{})), B.wt.put(p, yr, B.wt.put(p, xr, B.WtNone{})), ih(B.WtNone{}))

def put_comm(n: Nat, x: Word(n), y: Word(n), t: B.Wt) -> {B.wt.put(n, x, B.wt.put(n, y, t)) == B.wt.put(n, y, B.wt.put(n, x, t)) : B.Wt}:
  match n:
    case 0n:
      {==}
    case 1n+(+p):
      match x:
        case WCon{a, +xr}:
          match y:
            case WCon{b, +yr}:
              put_comm.k(a, b, p, xr, yr, t, s => put_comm(p, xr, yr, s))

def vs_comm(t: B.Wt, x: U32, y: U32) -> {B.vs.put(B.vs.put(t, y), x) == B.vs.put(B.vs.put(t, x), y) : B.Wt}:
  match x y:
    case U32{xw} U32{yw}:
      put_comm(32n, xw, yw, t)

# a unit moved within the list: the same set
def of_app(a: List<&2, U32>, +u: U32, +d: List<&2, U32>) ->
    {B.vs.of(List.append(&2, U32, a, Con{u, d})) == B.vs.put(B.vs.of(List.append(&2, U32, a, d)), u) : B.Wt}:
  match a:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      Equal.trans(B.Wt, B.vs.put(B.vs.of(List.append(&2, U32, t, Con{u, d})), h), B.vs.put(B.vs.put(B.vs.of(List.append(&2, U32, t, d)), u), h),
        B.vs.put(B.vs.put(B.vs.of(List.append(&2, U32, t, d)), h), u),
        Equal.cong(B.Wt, B.Wt, z => B.vs.put(z, h), B.vs.of(List.append(&2, U32, t, Con{u, d})), B.vs.put(B.vs.of(List.append(&2, U32, t, d)), u), of_app(t, u, d)),
        vs_comm(B.vs.of(List.append(&2, U32, t, d)), h, u))

# A list by position: split in two, its even positions first, read back
# as the list at double the position, and one more (`Pw`, each unit's
# calls in the fast walk, its uses in the dispositions)

def e_cons(-A: Data, +x: A, p: B.Eo<A>) -> {Con{x, B.eo.o(A, p)} == B.eo.e(A, B.eo.cons(A, x, p)) : List<&2, A>}:
  match p:
    case B.Eo{e, o}:
      {==}

def o_cons(-A: Data, +x: A, p: B.Eo<A>) -> {B.eo.e(A, p) == B.eo.o(A, B.eo.cons(A, x, p)) : List<&2, A>}:
  match p:
    case B.Eo{e, o}:
      {==}

def e_get.k(-A: Data, +x: A, +y: A, +r: List<&2, A>, i: Nat,
    ih: @j:Nat -> {List.get(&2, A, B.eo.e(A, B.eo.split(A, r)), j) == List.get(&2, A, r, Nat.double(j)) : Maybe<&2, A>}) ->
    {List.get(&2, A, Con{x, B.eo.e(A, B.eo.split(A, r))}, i) == List.get(&2, A, Con{x, Con{y, r}}, Nat.double(i)) : Maybe<&2, A>}:
  match i:
    case 0n:
      {==}
    case 1n+j:
      ih(j)

def e_get(-A: Data, xs: List<&2, A>, i: Nat) -> {List.get(&2, A, B.eo.e(A, B.eo.split(A, xs)), i) == List.get(&2, A, xs, Nat.double(i)) : Maybe<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, t}:
      match t:
        case Nil{}:
          match i:
            case 0n:
              {==}
            case 1n+j:
              {==}
        case Con{+y, +r}:
          %e_cons(A, x, B.eo.cons(A, y, B.eo.split(A, r))) :
            {List.get(&2, A, _, i) == List.get(&2, A, Con{x, Con{y, r}}, Nat.double(i)) : Maybe<&2, A>}
          %o_cons(A, y, B.eo.split(A, r)) :
            {List.get(&2, A, Con{x, _}, i) == List.get(&2, A, Con{x, Con{y, r}}, Nat.double(i)) : Maybe<&2, A>}
          e_get.k(A, x, y, r, i, j => e_get(A, r, j))

def o_get(-A: Data, xs: List<&2, A>, +i: Nat) -> {List.get(&2, A, B.eo.o(A, B.eo.split(A, xs)), i) == List.get(&2, A, xs, 1n+Nat.double(i)) : Maybe<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %o_cons(A, x, B.eo.split(A, t)) :
        {List.get(&2, A, _, i) == List.get(&2, A, Con{x, t}, 1n+Nat.double(i)) : Maybe<&2, A>}
      e_get(A, t, i)

# the tree answers as the list at the position the word reads
def pw_at(-A: Data, n: Nat, w: Word(n), xs: List<&2, A>) -> {B.pw.at(A, n, w, B.pw.build(A, n, xs)) == List.get(&2, A, xs, Word.to_nat(n, w)) : Maybe<&2, A>}:
  match n:
    case 0n:
      match xs:
        case Nil{}:
          {==}
        case Con{x, t}:
          {==}
    case 1n+(+p):
      match w:
        case WCon{b, +r}:
          match b:
            case True{}:
              match xs:
                case Nil{}:
                  {==}
                case Con{+x, +t}:
                  %o_get(A, Con{x, t}, Word.to_nat(p, r)) : {B.pw.at(A, p, r, B.pw.build(A, p, B.eo.o(A, B.eo.split(A, Con{x, t})))) == _ : Maybe<&2, A>}
                  pw_at(A, p, r, B.eo.o(A, B.eo.split(A, Con{x, t})))
            case False{}:
              match xs:
                case Nil{}:
                  {==}
                case Con{+x, +t}:
                  %e_get(A, Con{x, t}, Word.to_nat(p, r)) : {B.pw.at(A, p, r, B.pw.build(A, p, B.eo.e(A, B.eo.split(A, Con{x, t})))) == _ : Maybe<&2, A>}
                  pw_at(A, p, r, B.eo.e(A, B.eo.split(A, Con{x, t})))

# the tree of a list answers as List.get at a U32's value
def pw_get(-A: Data, xs: List<&2, A>, c: U32) -> {B.pw.get(A, B.pw.of(A, xs), c) == List.get(&2, A, xs, U32.to_nat(c)) : Maybe<&2, A>}:
  match c:
    case U32{w}:
      pw_at(A, 32n, w, xs)

# the calls table answers as ids.at
def cs_at(+cal: List<&2, List<&2, U32>>, +c: U32) -> {B.cs.at(B.ct.of(cal), c) == B.ids.at(cal, c) : List<&2, U32>}:
  %Equal.sym(Maybe<&2, List<&2, U32>>, B.pw.get(List<&2, U32>, B.pw.of(List<&2, U32>, cal), c), List.get(&2, List<&2, U32>, cal, U32.to_nat(c)), pw_get(List<&2, U32>, cal, c)) :
    {B.ids.or(_) == B.ids.at(cal, c) : List<&2, U32>}
  {==}

# The walk and the fast walk, step by step

# a state with the sets its lists make: those walked, those ordered, and
# those entered (the stack's units, then those walked)
def lift(s: B.Ds) -> B.Df:
  match s:
    case B.Ds{+stack, roots, +done, +order, ers}:
      B.Df{stack, roots, done, order, ers, B.vs.of(done), B.vs.of(order), B.vs.of(List.append(&2, U32, B.fms.units(stack), done))}

def ds_lift(s: B.Ds) -> {B.df.ds(lift(s)) == s : B.Ds}:
  match s:
    case B.Ds{stack, roots, done, order, ers}:
      {==}

def root_lift.k(seen: Bool, +r: U32, +rt: List<&2, U32>, +d: List<&2, U32>, +o: List<&2, U32>, +e: List<&2, B.Er>, +cal: List<&2, List<&2, U32>>) ->
    {B.df.root.k(seen, r, rt, d, o, e, B.vs.of(d), B.vs.of(o), B.vs.of(d), B.ct.of(cal)) == lift(B.ds.root.k(seen, r, rt, d, o, e, cal)) : B.Df}:
  match seen:
    case True{}:
      {==}
    case False{}:
      %cs_at(cal, r) : {B.df.root.k(False{}, r, rt, d, o, e, B.vs.of(d), B.vs.of(o), B.vs.of(d), B.ct.of(cal)) ==
        B.Df{[B.Fm{r, _}], rt, d, o, e, B.vs.of(d), B.vs.of(o), B.vs.put(B.vs.of(d), r)} : B.Df}
      {==}

# the lifted state a unit held back leaves, its entered set given
def lift.done.f(+u: U32, +st: List<&2, B.Fm>, +roots: List<&2, U32>, +d: List<&2, U32>, +o: List<&2, U32>, +e: List<&2, B.Er>, +obs: List<&2, B.Ob>, +us: List<&2, B.Un>, ve: B.Wt) -> B.Df:
  B.Df{st, roots, Con{u, d}, o,
    B.when(List<&2, B.Er>, List.is_empty(&2, B.Er, e),
      w => [B.Er{B.node.no(B.un.node(B.un.at(us, u))), B.text(B.un.name(obs, us, u)) ++ ": Blend's walk reached it before its callees, a fault of Blend's"}],
      w => e), B.vs.put(B.vs.of(d), u), B.vs.of(o), ve}

def done_lift.k(ok: Bool, +u: U32, +st: List<&2, B.Fm>, +roots: List<&2, U32>, +d: List<&2, U32>, +o: List<&2, U32>, +e: List<&2, B.Er>, +obs: List<&2, B.Ob>, +us: List<&2, B.Un>) ->
    {B.df.done.k(ok, u, st, roots, d, o, e, B.vs.of(d), B.vs.of(o), B.vs.of(Con{u, List.append(&2, U32, B.fms.units(st), d)}), obs, us) == lift(B.ds.done.k(ok, u, st, roots, d, o, e, obs, us)) : B.Df}:
  match ok:
    case True{}:
      %Equal.sym(B.Wt, B.vs.of(List.append(&2, U32, B.fms.units(st), Con{u, d})), B.vs.put(B.vs.of(List.append(&2, U32, B.fms.units(st), d)), u), of_app(B.fms.units(st), u, d)) :
        {B.df.done.k(True{}, u, st, roots, d, o, e, B.vs.of(d), B.vs.of(o), B.vs.of(Con{u, List.append(&2, U32, B.fms.units(st), d)}), obs, us) ==
          B.Df{st, roots, Con{u, d}, Con{u, o}, e, B.vs.put(B.vs.of(d), u), B.vs.put(B.vs.of(o), u), _} : B.Df}
      {==}
    case False{}:
      %Equal.sym(B.Wt, B.vs.of(List.append(&2, U32, B.fms.units(st), Con{u, d})), B.vs.put(B.vs.of(List.append(&2, U32, B.fms.units(st), d)), u), of_app(B.fms.units(st), u, d)) :
        {B.df.done.k(False{}, u, st, roots, d, o, e, B.vs.of(d), B.vs.of(o), B.vs.of(Con{u, List.append(&2, U32, B.fms.units(st), d)}), obs, us) ==
          lift.done.f(u, st, roots, d, o, e, obs, us, _) : B.Df}
      {==}

def call_lift.k(seen: Bool, cyc: Bool, +c: U32, +u: U32, +rs: List<&2, U32>, +st: List<&2, B.Fm>, +roots: List<&2, U32>, +d: List<&2, U32>, +o: List<&2, U32>,
    +e: List<&2, B.Er>, +cal: List<&2, List<&2, U32>>, +obs: List<&2, B.Ob>, +us: List<&2, B.Un>) ->
    {B.df.call.k(seen, Bool.or(cyc, seen), c, u, rs, st, roots, d, o, e, B.vs.of(d), B.vs.of(o), B.vs.of(Con{u, List.append(&2, U32, B.fms.units(st), d)}), B.ct.of(cal), obs, us) ==
      lift(B.ds.call.k(seen, cyc, c, u, rs, st, roots, d, o, e, cal, obs, us)) : B.Df}:
  match seen cyc:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      %cs_at(cal, c) : {B.df.call.k(False{}, False{}, c, u, rs, st, roots, d, o, e, B.vs.of(d), B.vs.of(o), B.vs.of(Con{u, List.append(&2, U32, B.fms.units(st), d)}), B.ct.of(cal), obs, us) ==
        B.Df{Con{B.Fm{c, _}, Con{B.Fm{u, rs}, st}}, roots, d, o, e, B.vs.of(d), B.vs.of(o), B.vs.put(B.vs.of(Con{u, List.append(&2, U32, B.fms.units(st), d)}), c)} : B.Df}
      {==}

# from a lifted state, a step of the fast walk is the lifted step of the
# walk: each of its lookups answers as the search it stands for
def step_lift(s: B.Ds, +cal: List<&2, List<&2, U32>>, +obs: List<&2, B.Ob>, +us: List<&2, B.Un>) ->
    {B.df.step(lift(s), B.ct.of(cal), obs, us) == lift(B.ds.step(s, cal, obs, us)) : B.Df}:
  match s:
    case B.Ds{stack, +roots, +done, +order, +ers}:
      match stack:
        case Nil{}:
          match roots:
            case Nil{}:
              {==}
            case Con{+r, +rt}:
              %Equal.sym(Bool, B.vs.has(B.vs.of(done), r), B.has(done, r), vs_of(done, r)) :
                {B.df.root.k(_, r, rt, done, order, ers, B.vs.of(done), B.vs.of(order), B.vs.of(done), B.ct.of(cal)) ==
                  lift(B.ds.root.k(B.has(done, r), r, rt, done, order, ers, cal)) : B.Df}
              root_lift.k(B.has(done, r), r, rt, done, order, ers, cal)
        case Con{f, +st}:
          match f:
            case B.Fm{+u, rest}:
              match rest:
                case Nil{}:
                  %Equal.sym(List<&2, U32>, B.cs.at(B.ct.of(cal), u), B.ids.at(cal, u), cs_at(cal, u)) :
                    {B.df.done.k(B.vs.all(_, B.vs.of(order)), u, st, roots, done, order, ers, B.vs.of(done), B.vs.of(order), B.vs.of(Con{u, List.append(&2, U32, B.fms.units(st), done)}), obs, us) ==
                      lift(B.ds.done.k(B.all.in(B.ids.at(cal, u), order), u, st, roots, done, order, ers, obs, us)) : B.Df}
                  %Equal.sym(Bool, B.vs.all(B.ids.at(cal, u), B.vs.of(order)), B.all.in(B.ids.at(cal, u), order), vs_all(B.ids.at(cal, u), order)) :
                    {B.df.done.k(_, u, st, roots, done, order, ers, B.vs.of(done), B.vs.of(order), B.vs.of(Con{u, List.append(&2, U32, B.fms.units(st), done)}), obs, us) ==
                      lift(B.ds.done.k(B.all.in(B.ids.at(cal, u), order), u, st, roots, done, order, ers, obs, us)) : B.Df}
                  done_lift.k(B.all.in(B.ids.at(cal, u), order), u, st, roots, done, order, ers, obs, us)
                case Con{+c, +rs}:
                  %Equal.sym(Bool, B.vs.has(B.vs.of(done), c), B.has(done, c), vs_of(done, c)) :
                    {B.df.call.k(_, B.vs.has(B.vs.of(Con{u, List.append(&2, U32, B.fms.units(st), done)}), c), c, u, rs, st, roots, done, order, ers, B.vs.of(done), B.vs.of(order), B.vs.of(Con{u, List.append(&2, U32, B.fms.units(st), done)}), B.ct.of(cal), obs, us) ==
                      lift(B.ds.call.k(B.has(done, c), B.has(Con{u, B.fms.units(st)}, c), c, u, rs, st, roots, done, order, ers, cal, obs, us)) : B.Df}
                  %Equal.sym(Bool, B.vs.has(B.vs.of(Con{u, List.append(&2, U32, B.fms.units(st), done)}), c), B.has(Con{u, List.append(&2, U32, B.fms.units(st), done)}, c), vs_of(Con{u, List.append(&2, U32, B.fms.units(st), done)}, c)) :
                    {B.df.call.k(B.has(done, c), _, c, u, rs, st, roots, done, order, ers, B.vs.of(done), B.vs.of(order), B.vs.of(Con{u, List.append(&2, U32, B.fms.units(st), done)}), B.ct.of(cal), obs, us) ==
                      lift(B.ds.call.k(B.has(done, c), B.has(Con{u, B.fms.units(st)}, c), c, u, rs, st, roots, done, order, ers, cal, obs, us)) : B.Df}
                  %has_app(Con{u, B.fms.units(st)}, done, c) :
                    {B.df.call.k(B.has(done, c), _, c, u, rs, st, roots, done, order, ers, B.vs.of(done), B.vs.of(order), B.vs.of(Con{u, List.append(&2, U32, B.fms.units(st), done)}), B.ct.of(cal), obs, us) ==
                      lift(B.ds.call.k(B.has(done, c), B.has(Con{u, B.fms.units(st)}, c), c, u, rs, st, roots, done, order, ers, cal, obs, us)) : B.Df}
                  call_lift.k(B.has(done, c), B.has(Con{u, B.fms.units(st)}, c), c, u, rs, st, roots, done, order, ers, cal, obs, us)

# walking a lifted state is lifting the walk
def go_lift(n: Nat, +s: B.Ds, +cal: List<&2, List<&2, U32>>, +obs: List<&2, B.Ob>, +us: List<&2, B.Un>) ->
    {B.df.go(n, lift(s), B.ct.of(cal), obs, us) == lift(B.ds.go(n, s, cal, obs, us)) : B.Df}:
  match n:
    case 0n:
      {==}
    case 1n+(+k):
      %Equal.sym(B.Df, B.df.step(lift(s), B.ct.of(cal), obs, us), lift(B.ds.step(s, cal, obs, us)), step_lift(s, cal, obs, us)) :
        {B.df.go(k, _, B.ct.of(cal), obs, us) == lift(B.ds.go(k, B.ds.step(s, cal, obs, us), cal, obs, us)) : B.Df}
      go_lift(k, B.ds.step(s, cal, obs, us), cal, obs, us)

def Laws.order.fast(roots, cal, obs, us):
  %Equal.sym(B.Df, B.df.go(B.walk.fuel(roots, cal), lift(B.Ds{Nil{}, roots, Nil{}, Nil{}, Nil{}}), B.ct.of(cal), obs, us),
      lift(B.ds.go(B.walk.fuel(roots, cal), B.Ds{Nil{}, roots, Nil{}, Nil{}, Nil{}}, cal, obs, us)),
      go_lift(B.walk.fuel(roots, cal), B.Ds{Nil{}, roots, Nil{}, Nil{}, Nil{}}, cal, obs, us)) :
    {B.df.ds(_) == B.walk(roots, cal, obs, us) : B.Ds}
  ds_lift(B.ds.go(B.walk.fuel(roots, cal), B.Ds{Nil{}, roots, Nil{}, Nil{}, Nil{}}, cal, obs, us))

# What is emitted
# ---------------
#
# The writer and the names check, each a loop of its own over the order,
# against one list of the definitions emitted (`defs.of`).

def defs_app(a: List<&2, B.Dp>, +c: List<&2, B.Dp>, +e: B.Ec, b: B.Tb) ->
    {B.defs.put(List.append(&2, B.Dp, a, c), e, b) == B.defs.put(c, e, B.defs.put(a, e, b)) : B.Tb}:
  match a:
    case Nil{}:
      {==}
    case Con{d, t}:
      match d:
        case B.Dp{+x, +j}:
          defs_app(t, c, e, B.unit.put(e, x, j, b))

def defs_copies(n: Nat, +e: B.Ec, +x: U32, +j: U32, b: B.Tb) -> {B.defs.put(B.dps.copies(n, x, j), e, b) == B.copies.put(n, e, x, j, b) : B.Tb}:
  match n:
    case 0n:
      {==}
    case 1n+k:
      defs_copies(k, e, x, (j + 1 : U32), B.unit.put(e, x, j, b))

def unit_all(+e: B.Ec, +x: U32, mu: B.Mu, b: B.Tb) ->
    {B.copies.put(U32.to_nat(B.mu.m(mu)), e, x, 1, B.unit.put(e, x, 0, b)) == B.unit.all(e, x, mu, b) : B.Tb}:
  match mu:
    case B.Mu{+m, +kind}:
      {==}

def Laws.emit.defs(xs, e, b):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %unit_all(e, x, B.ec.mu(e, x), b) :
        {B.order.put(t, e, _) == B.defs.put(B.defs.of(Con{x, t}, e), e, b) : B.Tb}
      %Equal.sym(B.Tb, B.defs.put(List.append(&2, B.Dp, B.dps.copies(U32.to_nat(B.mu.m(B.ec.mu(e, x))), x, 1), B.defs.of(t, e)), e, B.unit.put(e, x, 0, b)), B.defs.put(B.defs.of(t, e), e, B.defs.put(B.dps.copies(U32.to_nat(B.mu.m(B.ec.mu(e, x))), x, 1), e, B.unit.put(e, x, 0, b))), defs_app(B.dps.copies(U32.to_nat(B.mu.m(B.ec.mu(e, x))), x, 1), B.defs.of(t, e), e, B.unit.put(e, x, 0, b))) :
        {B.order.put(t, e, B.copies.put(U32.to_nat(B.mu.m(B.ec.mu(e, x))), e, x, 1, B.unit.put(e, x, 0, b))) == _ : B.Tb}
      %Equal.sym(B.Tb, B.defs.put(B.dps.copies(U32.to_nat(B.mu.m(B.ec.mu(e, x))), x, 1), e, B.unit.put(e, x, 0, b)), B.copies.put(U32.to_nat(B.mu.m(B.ec.mu(e, x))), e, x, 1, B.unit.put(e, x, 0, b)), defs_copies(U32.to_nat(B.mu.m(B.ec.mu(e, x))), e, x, 1, B.unit.put(e, x, 0, b))) :
        {B.order.put(t, e, B.copies.put(U32.to_nat(B.mu.m(B.ec.mu(e, x))), e, x, 1, B.unit.put(e, x, 0, b))) == B.defs.put(B.defs.of(t, e), e, _) : B.Tb}
      Laws.emit.defs(t, e, B.copies.put(U32.to_nat(B.mu.m(B.ec.mu(e, x))), e, x, 1, B.unit.put(e, x, 0, b)))

def names_app(a: List<&2, B.Dp>, +c: List<&2, B.Dp>, +e: B.Ec) ->
    {List.append(&2, B.Nm, B.defs.names(a, e), B.defs.names(c, e)) == B.defs.names(List.append(&2, B.Dp, a, c), e) : List<&2, B.Nm>}:
  match a:
    case Nil{}:
      {==}
    case Con{d, t}:
      match d:
        case B.Dp{+x, +j}:
          %names_app(t, c, e) : {Con{B.Nm{B.own.name(e, x, j), x, B.node.no(B.un.node(B.ec.un(e, x)))}, List.append(&2, B.Nm, B.defs.names(t, e), B.defs.names(c, e))} ==
            Con{B.Nm{B.own.name(e, x, j), x, B.node.no(B.un.node(B.ec.un(e, x)))}, _} : List<&2, B.Nm>}
          {==}

def names_copies(n: Nat, +e: B.Ec, +x: U32, +j: U32) -> {B.names.copies(n, e, x, j) == B.defs.names(B.dps.copies(n, x, j), e) : List<&2, B.Nm>}:
  match n:
    case 0n:
      {==}
    case 1n+k:
      %names_copies(k, e, x, (j + 1 : U32)) : {Con{B.Nm{B.own.name(e, x, j), x, B.node.no(B.un.node(B.ec.un(e, x)))}, B.names.copies(k, e, x, (j + 1 : U32))} ==
        Con{B.Nm{B.own.name(e, x, j), x, B.node.no(B.un.node(B.ec.un(e, x)))}, _} : List<&2, B.Nm>}
      {==}

def Laws.emit.names(xs, e):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %Equal.sym(List<&2, B.Nm>, B.names.copies(1n+U32.to_nat(B.mu.m(B.ec.mu(e, x))), e, x, 0), B.defs.names(B.dps.copies(1n+U32.to_nat(B.mu.m(B.ec.mu(e, x))), x, 0), e), names_copies(1n+U32.to_nat(B.mu.m(B.ec.mu(e, x))), e, x, 0)) :
        {List.append(&2, B.Nm, _, B.names.all(t, e)) == B.defs.names(B.defs.of(Con{x, t}, e), e) : List<&2, B.Nm>}
      %Equal.sym(List<&2, B.Nm>, B.names.all(t, e), B.defs.names(B.defs.of(t, e), e), Laws.emit.names(t, e)) :
        {List.append(&2, B.Nm, B.defs.names(B.dps.copies(1n+U32.to_nat(B.mu.m(B.ec.mu(e, x))), x, 0), e), _) == B.defs.names(B.defs.of(Con{x, t}, e), e) : List<&2, B.Nm>}
      names_app(B.dps.copies(1n+U32.to_nat(B.mu.m(B.ec.mu(e, x))), x, 0), B.defs.of(t, e), e)

# The dispositions
# ----------------
#
# mults hands each unit's uses on to the units it uses, in a table on the
# units' bits; the specification searches the units emitted for them. At
# a unit's turn the table holds its uses by the units already taken
# (`pa_at`), and in a callee-first order no unit yet to come uses it
# (`rev_none`), nor does it use itself (`self_none`), so that both see
# the same uses, and make the same disposition.

def mpick(-A: Data, b: Bool, x: Maybe<&2, A>, y: Maybe<&2, A>) -> Maybe<&2, A>:
  match b:
    case True{}:
      x
    case False{}:
      y

def get_none(-A: Data, n: Nat, c: Word(n)) -> {B.wm.get(A, n, c, B.WmNone{}) == None{} : Maybe<&2, A>}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match c:
        case WCon{b, r}:
          match b:
            case True{}:
              {==}
            case False{}:
              {==}

def get_put.k(-A: Data, a: Bool, b: Bool, +p: Nat, +xr: Word(p), +cr: Word(p), +v: A, t: B.Wm<A>,
    ih: @s:B.Wm<A> -> {B.wm.get(A, p, cr, B.wm.put(A, p, xr, v, s)) == mpick(A, Cmp.is_eq(Word.cmp(p, xr, cr)), Some{v}, B.wm.get(A, p, cr, s)) : Maybe<&2, A>}) ->
    {B.wm.get(A, 1n+p, WCon{b, cr}, B.wm.put(A, 1n+p, WCon{a, xr}, v, t)) ==
      mpick(A, Bool.and(Cmp.is_eq(Word.cmp(p, xr, cr)), Cmp.is_eq(Bool.cmp(a, b))), Some{v}, B.wm.get(A, 1n+p, WCon{b, cr}, t)) : Maybe<&2, A>}:
  match a b:
    case True{} True{}:
      match t:
        case B.WmNode{f, tt}:
          %Equal.sym(Bool, Bool.and(Cmp.is_eq(Word.cmp(p, xr, cr)), True{}), Cmp.is_eq(Word.cmp(p, xr, cr)), MB.and_true(Cmp.is_eq(Word.cmp(p, xr, cr)))) :
            {B.wm.get(A, 1n+p, WCon{True{}, cr}, B.wm.put(A, 1n+p, WCon{True{}, xr}, v, B.WmNode{f, tt})) == mpick(A, _, Some{v}, B.wm.get(A, 1n+p, WCon{True{}, cr}, B.WmNode{f, tt})) : Maybe<&2, A>}
          ih(tt)
        case B.WmNone{}:
          %Equal.sym(Bool, Bool.and(Cmp.is_eq(Word.cmp(p, xr, cr)), True{}), Cmp.is_eq(Word.cmp(p, xr, cr)), MB.and_true(Cmp.is_eq(Word.cmp(p, xr, cr)))) :
            {B.wm.get(A, 1n+p, WCon{True{}, cr}, B.wm.put(A, 1n+p, WCon{True{}, xr}, v, B.WmNone{})) == mpick(A, _, Some{v}, B.wm.get(A, 1n+p, WCon{True{}, cr}, B.WmNone{})) : Maybe<&2, A>}
          %get_none(A, p, cr) : {B.wm.get(A, p, cr, B.wm.put(A, p, xr, v, B.WmNone{})) == mpick(A, Cmp.is_eq(Word.cmp(p, xr, cr)), Some{v}, _) : Maybe<&2, A>}
          ih(B.WmNone{})
        case B.WmLeaf{l}:
          %Equal.sym(Bool, Bool.and(Cmp.is_eq(Word.cmp(p, xr, cr)), True{}), Cmp.is_eq(Word.cmp(p, xr, cr)), MB.and_true(Cmp.is_eq(Word.cmp(p, xr, cr)))) :
            {B.wm.get(A, 1n+p, WCon{True{}, cr}, B.wm.put(A, 1n+p, WCon{True{}, xr}, v, B.WmLeaf{l})) == mpick(A, _, Some{v}, B.wm.get(A, 1n+p, WCon{True{}, cr}, B.WmLeaf{l})) : Maybe<&2, A>}
          %get_none(A, p, cr) : {B.wm.get(A, p, cr, B.wm.put(A, p, xr, v, B.WmNone{})) == mpick(A, Cmp.is_eq(Word.cmp(p, xr, cr)), Some{v}, _) : Maybe<&2, A>}
          ih(B.WmNone{})
    case True{} False{}:
      match t:
        case B.WmNode{f, tt}:
          %Equal.sym(Bool, Bool.and(Cmp.is_eq(Word.cmp(p, xr, cr)), False{}), False{}, MB.and_false(Cmp.is_eq(Word.cmp(p, xr, cr)))) :
            {B.wm.get(A, 1n+p, WCon{False{}, cr}, B.wm.put(A, 1n+p, WCon{True{}, xr}, v, B.WmNode{f, tt})) == mpick(A, _, Some{v}, B.wm.get(A, 1n+p, WCon{False{}, cr}, B.WmNode{f, tt})) : Maybe<&2, A>}
          {==}
        case B.WmNone{}:
          %Equal.sym(Bool, Bool.and(Cmp.is_eq(Word.cmp(p, xr, cr)), False{}), False{}, MB.and_false(Cmp.is_eq(Word.cmp(p, xr, cr)))) :
            {B.wm.get(A, 1n+p, WCon{False{}, cr}, B.wm.put(A, 1n+p, WCon{True{}, xr}, v, B.WmNone{})) == mpick(A, _, Some{v}, B.wm.get(A, 1n+p, WCon{False{}, cr}, B.WmNone{})) : Maybe<&2, A>}
          get_none(A, p, cr)
        case B.WmLeaf{l}:
          %Equal.sym(Bool, Bool.and(Cmp.is_eq(Word.cmp(p, xr, cr)), False{}), False{}, MB.and_false(Cmp.is_eq(Word.cmp(p, xr, cr)))) :
            {B.wm.get(A, 1n+p, WCon{False{}, cr}, B.wm.put(A, 1n+p, WCon{True{}, xr}, v, B.WmLeaf{l})) == mpick(A, _, Some{v}, B.wm.get(A, 1n+p, WCon{False{}, cr}, B.WmLeaf{l})) : Maybe<&2, A>}
          get_none(A, p, cr)
    case False{} True{}:
      match t:
        case B.WmNode{f, tt}:
          %Equal.sym(Bool, Bool.and(Cmp.is_eq(Word.cmp(p, xr, cr)), False{}), False{}, MB.and_false(Cmp.is_eq(Word.cmp(p, xr, cr)))) :
            {B.wm.get(A, 1n+p, WCon{True{}, cr}, B.wm.put(A, 1n+p, WCon{False{}, xr}, v, B.WmNode{f, tt})) == mpick(A, _, Some{v}, B.wm.get(A, 1n+p, WCon{True{}, cr}, B.WmNode{f, tt})) : Maybe<&2, A>}
          {==}
        case B.WmNone{}:
          %Equal.sym(Bool, Bool.and(Cmp.is_eq(Word.cmp(p, xr, cr)), False{}), False{}, MB.and_false(Cmp.is_eq(Word.cmp(p, xr, cr)))) :
            {B.wm.get(A, 1n+p, WCon{True{}, cr}, B.wm.put(A, 1n+p, WCon{False{}, xr}, v, B.WmNone{})) == mpick(A, _, Some{v}, B.wm.get(A, 1n+p, WCon{True{}, cr}, B.WmNone{})) : Maybe<&2, A>}
          get_none(A, p, cr)
        case B.WmLeaf{l}:
          %Equal.sym(Bool, Bool.and(Cmp.is_eq(Word.cmp(p, xr, cr)), False{}), False{}, MB.and_false(Cmp.is_eq(Word.cmp(p, xr, cr)))) :
            {B.wm.get(A, 1n+p, WCon{True{}, cr}, B.wm.put(A, 1n+p, WCon{False{}, xr}, v, B.WmLeaf{l})) == mpick(A, _, Some{v}, B.wm.get(A, 1n+p, WCon{True{}, cr}, B.WmLeaf{l})) : Maybe<&2, A>}
          get_none(A, p, cr)
    case False{} False{}:
      match t:
        case B.WmNode{f, tt}:
          %Equal.sym(Bool, Bool.and(Cmp.is_eq(Word.cmp(p, xr, cr)), True{}), Cmp.is_eq(Word.cmp(p, xr, cr)), MB.and_true(Cmp.is_eq(Word.cmp(p, xr, cr)))) :
            {B.wm.get(A, 1n+p, WCon{False{}, cr}, B.wm.put(A, 1n+p, WCon{False{}, xr}, v, B.WmNode{f, tt})) == mpick(A, _, Some{v}, B.wm.get(A, 1n+p, WCon{False{}, cr}, B.WmNode{f, tt})) : Maybe<&2, A>}
          ih(f)
        case B.WmNone{}:
          %Equal.sym(Bool, Bool.and(Cmp.is_eq(Word.cmp(p, xr, cr)), True{}), Cmp.is_eq(Word.cmp(p, xr, cr)), MB.and_true(Cmp.is_eq(Word.cmp(p, xr, cr)))) :
            {B.wm.get(A, 1n+p, WCon{False{}, cr}, B.wm.put(A, 1n+p, WCon{False{}, xr}, v, B.WmNone{})) == mpick(A, _, Some{v}, B.wm.get(A, 1n+p, WCon{False{}, cr}, B.WmNone{})) : Maybe<&2, A>}
          %get_none(A, p, cr) : {B.wm.get(A, p, cr, B.wm.put(A, p, xr, v, B.WmNone{})) == mpick(A, Cmp.is_eq(Word.cmp(p, xr, cr)), Some{v}, _) : Maybe<&2, A>}
          ih(B.WmNone{})
        case B.WmLeaf{l}:
          %Equal.sym(Bool, Bool.and(Cmp.is_eq(Word.cmp(p, xr, cr)), True{}), Cmp.is_eq(Word.cmp(p, xr, cr)), MB.and_true(Cmp.is_eq(Word.cmp(p, xr, cr)))) :
            {B.wm.get(A, 1n+p, WCon{False{}, cr}, B.wm.put(A, 1n+p, WCon{False{}, xr}, v, B.WmLeaf{l})) == mpick(A, _, Some{v}, B.wm.get(A, 1n+p, WCon{False{}, cr}, B.WmLeaf{l})) : Maybe<&2, A>}
          %get_none(A, p, cr) : {B.wm.get(A, p, cr, B.wm.put(A, p, xr, v, B.WmNone{})) == mpick(A, Cmp.is_eq(Word.cmp(p, xr, cr)), Some{v}, _) : Maybe<&2, A>}
          ih(B.WmNone{})

# a value put at a word, then one asked for: the value where they are
# equal, else what was there
def get_put(-A: Data, n: Nat, x: Word(n), c: Word(n), +v: A, t: B.Wm<A>) ->
    {B.wm.get(A, n, c, B.wm.put(A, n, x, v, t)) == mpick(A, Cmp.is_eq(Word.cmp(n, x, c)), Some{v}, B.wm.get(A, n, c, t)) : Maybe<&2, A>}:
  match n:
    case 0n:
      {==}
    case 1n+(+p):
      match x:
        case WCon{+a, +xr}:
          match c:
            case WCon{+b, +cr}:
              %fin_eq(a, b, Word.cmp(p, xr, cr)) :
                {B.wm.get(A, 1n+p, WCon{b, cr}, B.wm.put(A, 1n+p, WCon{a, xr}, v, t)) == mpick(A, _, Some{v}, B.wm.get(A, 1n+p, WCon{b, cr}, t)) : Maybe<&2, A>}
              get_put.k(A, a, b, p, xr, cr, v, t, s => get_put(A, p, xr, cr, v, s))

def um_get_put(-A: Data, +t: B.Wm<A>, x: U32, c: U32, +v: A) ->
    {B.um.get(A, B.um.put(A, t, x, v), c) == mpick(A, U32.is_eq(x, c), Some{v}, B.um.get(A, t, c)) : Maybe<&2, A>}:
  match x c:
    case U32{xw} U32{cw}:
      get_put(A, 32n, xw, cw, v, t)

def um_get_none(-A: Data, c: U32) -> {B.um.get(A, B.WmNone{}, c) == None{} : Maybe<&2, A>}:
  match c:
    case U32{w}:
      get_none(A, 32n, w)

# a user's uses handed on: each its callee's, first, in the user's order
def pend_uses.k(hit: Bool, +c: U32, +y: U32, +u: U32, +no: U32, +t: List<&2, B.Ru>, +pp: B.Wm<List<&2, B.Ru>>, +p: B.Wm<List<&2, B.Ru>>,
    +e: {hit == U32.is_eq(c, y) : Bool},
    +ih: {B.pend.at(pp, y) == List.append(&2, B.Ru, B.uses.in(t, u, y), B.pend.at(p, y)) : List<&2, B.Ru>}) ->
    {B.rus.or(mpick(List<&2, B.Ru>, hit, Some{Con{B.Ru{u, no}, B.pend.at(pp, c)}}, B.um.get(List<&2, B.Ru>, pp, y))) ==
      List.append(&2, B.Ru, B.uses.in.k(hit, u, no, B.uses.in(t, u, y)), B.pend.at(p, y)) : List<&2, B.Ru>}:
  match hit:
    case True{}:
      %Equal.sym(U32, c, y, u32_eq_of_is_eq(c, y, Equal.sym(Bool, True{}, U32.is_eq(c, y), e))) :
        {Con{B.Ru{u, no}, B.pend.at(pp, _)} == Con{B.Ru{u, no}, List.append(&2, B.Ru, B.uses.in(t, u, y), B.pend.at(p, y))} : List<&2, B.Ru>}
      Equal.cong(List<&2, B.Ru>, List<&2, B.Ru>, z => Con{B.Ru{u, no}, z}, B.pend.at(pp, y), List.append(&2, B.Ru, B.uses.in(t, u, y), B.pend.at(p, y)), ih)
    case False{}:
      ih

def pend_uses(rs: List<&2, B.Ru>, +u: U32, +p: B.Wm<List<&2, B.Ru>>, +y: U32) ->
    {B.pend.at(B.pend.uses(rs, u, p), y) == List.append(&2, B.Ru, B.uses.in(rs, u, y), B.pend.at(p, y)) : List<&2, B.Ru>}:
  match rs:
    case Nil{}:
      {==}
    case Con{r, +t}:
      match r:
        case B.Ru{+c, +no}:
          %Equal.sym(Maybe<&2, List<&2, B.Ru>>, B.um.get(List<&2, B.Ru>, B.um.put(List<&2, B.Ru>, B.pend.uses(t, u, p), c, Con{B.Ru{u, no}, B.pend.at(B.pend.uses(t, u, p), c)}), y),
              mpick(List<&2, B.Ru>, U32.is_eq(c, y), Some{Con{B.Ru{u, no}, B.pend.at(B.pend.uses(t, u, p), c)}}, B.um.get(List<&2, B.Ru>, B.pend.uses(t, u, p), y)),
              um_get_put(List<&2, B.Ru>, B.pend.uses(t, u, p), c, y, Con{B.Ru{u, no}, B.pend.at(B.pend.uses(t, u, p), c)})) :
            {B.rus.or(_) == List.append(&2, B.Ru, B.uses.in(Con{B.Ru{c, no}, t}, u, y), B.pend.at(p, y)) : List<&2, B.Ru>}
          pend_uses.k(U32.is_eq(c, y), c, y, u, no, t, B.pend.uses(t, u, p), p, {==}, pend_uses(t, u, p, y))

# the table after the units q, the last taken first
def pa(q: List<&2, U32>, +rt: B.Pw<List<&2, B.Ru>>) -> B.Wm<List<&2, B.Ru>>:
  match q:
    case Nil{}:
      B.WmNone{}
    case Con{+x, t}:
      B.pend.uses(B.rus.or(B.pw.get(List<&2, B.Ru>, rt, x)), x, pa(t, rt))

# it holds each unit's uses by the units q, in q's order
def pa_at(q: List<&2, U32>, +rss: List<&2, List<&2, B.Ru>>, +y: U32) -> {B.pend.at(pa(q, B.pw.of(List<&2, B.Ru>, rss)), y) == B.uses.of(q, rss, y) : List<&2, B.Ru>}:
  match q:
    case Nil{}:
      %Equal.sym(Maybe<&2, List<&2, B.Ru>>, B.um.get(List<&2, B.Ru>, B.WmNone{}, y), None{}, um_get_none(List<&2, B.Ru>, y)) : {B.rus.or(_) == Nil{} : List<&2, B.Ru>}
      {==}
    case Con{+e, +t}:
      %Equal.sym(List<&2, B.Ru>, B.pend.at(B.pend.uses(B.rus.or(B.pw.get(List<&2, B.Ru>, B.pw.of(List<&2, B.Ru>, rss), e)), e, pa(t, B.pw.of(List<&2, B.Ru>, rss))), y),
          List.append(&2, B.Ru, B.uses.in(B.rus.or(B.pw.get(List<&2, B.Ru>, B.pw.of(List<&2, B.Ru>, rss), e)), e, y), B.pend.at(pa(t, B.pw.of(List<&2, B.Ru>, rss)), y)),
          pend_uses(B.rus.or(B.pw.get(List<&2, B.Ru>, B.pw.of(List<&2, B.Ru>, rss), e)), e, pa(t, B.pw.of(List<&2, B.Ru>, rss)), y)) :
        {_ == B.uses.of(Con{e, t}, rss, y) : List<&2, B.Ru>}
      %Equal.sym(Maybe<&2, List<&2, B.Ru>>, B.pw.get(List<&2, B.Ru>, B.pw.of(List<&2, B.Ru>, rss), e), List.get(&2, List<&2, B.Ru>, rss, U32.to_nat(e)), pw_get(List<&2, B.Ru>, rss, e)) :
        {List.append(&2, B.Ru, B.uses.in(B.rus.or(_), e, y), B.pend.at(pa(t, B.pw.of(List<&2, B.Ru>, rss)), y)) == B.uses.of(Con{e, t}, rss, y) : List<&2, B.Ru>}
      %Equal.sym(List<&2, B.Ru>, B.pend.at(pa(t, B.pw.of(List<&2, B.Ru>, rss)), y), B.uses.of(t, rss, y), pa_at(t, rss, y)) :
        {List.append(&2, B.Ru, B.uses.in(B.rus.at(rss, e), e, y), _) == B.uses.of(Con{e, t}, rss, y) : List<&2, B.Ru>}
      {==}

# a unit's calls are those of its uses
def calls_at(rss: List<&2, List<&2, B.Ru>>, n: Nat) -> {B.ids.or(List.get(&2, List<&2, U32>, B.calls(rss), n)) == B.ru.us(B.rus.or(List.get(&2, List<&2, B.Ru>, rss, n))) : List<&2, U32>}:
  match rss:
    case Nil{}:
      {==}
    case Con{rs, t}:
      match n:
        case 0n:
          {==}
        case 1n+k:
          calls_at(t, k)

def uses_in_none.k(hit: Bool, +e: U32, +x: U32, +no: U32, +t: List<&2, B.Ru>,
    +h: {Bool.or(hit, B.has(B.ru.us(t), x)) == False{} : Bool},
    ih: {B.has(B.ru.us(t), x) == False{} : Bool} -> {B.uses.in(t, e, x) == Nil{} : List<&2, B.Ru>}) ->
    {B.uses.in.k(hit, e, no, B.uses.in(t, e, x)) == Nil{} : List<&2, B.Ru>}:
  match hit:
    case True{}:
      Empty.absurd({B.uses.in.k(True{}, e, no, B.uses.in(t, e, x)) == Nil{} : List<&2, B.Ru>}, MB.true_ne_false()(h))
    case False{}:
      ih(h)

# no use of x among uses that do not call x
def uses_in_none(rs: List<&2, B.Ru>, +e: U32, +x: U32, +h: {B.has(B.ru.us(rs), x) == False{} : Bool}) -> {B.uses.in(rs, e, x) == Nil{} : List<&2, B.Ru>}:
  match rs:
    case Nil{}:
      {==}
    case Con{r, +t}:
      match r:
        case B.Ru{+u, +no}:
          uses_in_none.k(U32.is_eq(u, x), e, x, no, t, h, g => uses_in_none(t, e, x, g))

def not_has_sub.k(b: Bool, +xs: List<&2, U32>, +ys: List<&2, U32>, +x: U32, +e: {b == B.has(xs, x) : Bool}, +hs: {B.all.in(xs, ys) == True{} : Bool},
    +hn: {B.has(ys, x) == False{} : Bool}) -> {B.has(xs, x) == False{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({B.has(xs, x) == False{} : Bool},
        MB.true_ne_false()(Equal.trans(Bool, True{}, B.has(ys, x), False{}, Equal.sym(Bool, B.has(ys, x), True{}, has_sub(xs, ys, x, hs, Equal.sym(Bool, True{}, B.has(xs, x), e))), hn)))
    case False{}:
      Equal.sym(Bool, False{}, B.has(xs, x), e)

# x, missing from ys, is missing from what ys holds
def not_has_sub(+xs: List<&2, U32>, +ys: List<&2, U32>, +x: U32, +hs: {B.all.in(xs, ys) == True{} : Bool}, +hn: {B.has(ys, x) == False{} : Bool}) ->
    {B.has(xs, x) == False{} : Bool}:
  not_has_sub.k(B.has(xs, x), xs, ys, x, {==}, hs, hn)

def calls_in_mono(r: List<&2, U32>, +cal: List<&2, List<&2, U32>>, +ys: List<&2, U32>, +zs: List<&2, U32>, +h: {B.calls.in(r, cal, ys) == True{} : Bool}, +s: {B.all.in(ys, zs) == True{} : Bool}) ->
    {B.calls.in(r, cal, zs) == True{} : Bool}:
  match r:
    case Nil{}:
      {==}
    case Con{+u, +t}:
      and_intro(B.all.in(B.ids.at(cal, u), zs), B.calls.in(t, cal, zs),
        sub_trans(B.ids.at(cal, u), ys, zs, MB.eq_true_of_and_left(B.all.in(B.ids.at(cal, u), ys), B.calls.in(t, cal, ys), h), s),
        calls_in_mono(t, cal, ys, zs, MB.eq_true_of_and_right(B.all.in(B.ids.at(cal, u), ys), B.calls.in(t, cal, ys), h), s))

# in a callee-first order, each unit's calls are among the order
def ordered_closed(r: List<&2, U32>, +cal: List<&2, List<&2, U32>>, +h: {B.ordered(r, cal) == True{} : Bool}) -> {B.calls.in(r, cal, r) == True{} : Bool}:
  match r:
    case Nil{}:
      {==}
    case Con{+u, +t}:
      and_intro(B.all.in(B.ids.at(cal, u), Con{u, t}), B.calls.in(t, cal, Con{u, t}),
        all_in_mono(B.ids.at(cal, u), t, u, MB.eq_true_of_and_left(B.all.in(B.ids.at(cal, u), t), B.ordered(t, cal), h)),
        calls_in_mono(t, cal, t, Con{u, t}, ordered_closed(t, cal, MB.eq_true_of_and_right(B.all.in(B.ids.at(cal, u), t), B.ordered(t, cal), h)), sub_cons(t, u)))

# a unit's uses of y, where its calls are among ys and y is not
def use_none(+rss: List<&2, List<&2, B.Ru>>, +e: U32, +y: U32, +ys: List<&2, U32>, +h: {B.all.in(B.ids.at(B.calls(rss), e), ys) == True{} : Bool},
    +hy: {B.has(ys, y) == False{} : Bool}) -> {B.uses.in(B.rus.at(rss, e), e, y) == Nil{} : List<&2, B.Ru>}:
  uses_in_none(B.rus.at(rss, e), e, y,
    ME.subst(List<&2, U32>, z => {B.has(z, y) == False{} : Bool}, B.ids.at(B.calls(rss), e), B.ru.us(B.rus.at(rss, e)),
      calls_at(rss, U32.to_nat(e)), not_has_sub(B.ids.at(B.calls(rss), e), ys, y, h, hy)))

# the units r, reversed onto a, use y no more than a does, where their
# calls are among ys and y is not
def rev_none(r: List<&2, U32>, +a: List<&2, U32>, +rss: List<&2, List<&2, B.Ru>>, +y: U32, +ys: List<&2, U32>, +h: {B.calls.in(r, B.calls(rss), ys) == True{} : Bool},
    +hy: {B.has(ys, y) == False{} : Bool}) -> {B.uses.of(List.reverse.go(&2, U32, r, a), rss, y) == B.uses.of(a, rss, y) : List<&2, B.Ru>}:
  match r:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      Equal.trans(List<&2, B.Ru>, B.uses.of(List.reverse.go(&2, U32, t, Con{e, a}), rss, y), B.uses.of(Con{e, a}, rss, y), B.uses.of(a, rss, y),
        rev_none(t, Con{e, a}, rss, y, ys, MB.eq_true_of_and_right(B.all.in(B.ids.at(B.calls(rss), e), ys), B.calls.in(t, B.calls(rss), ys), h), hy),
        Equal.cong(List<&2, B.Ru>, List<&2, B.Ru>, z => List.append(&2, B.Ru, z, B.uses.of(a, rss, y)), B.uses.in(B.rus.at(rss, e), e, y), Nil{},
          use_none(rss, e, y, ys, MB.eq_true_of_and_left(B.all.in(B.ids.at(B.calls(rss), e), ys), B.calls.in(t, B.calls(rss), ys), h), hy)))

# at x's turn, the uses of x by the units the order emits are those by
# the units already taken
def at_turn(+x: U32, +r: List<&2, U32>, +q: List<&2, U32>, +rss: List<&2, List<&2, B.Ru>>, +h1: {B.ordered(Con{x, r}, B.calls(rss)) == True{} : Bool},
    +h2: {B.distinct(Con{x, r}) == True{} : Bool}) ->
    {B.uses.of(List.reverse.go(&2, U32, r, Con{x, q}), rss, x) == B.uses.of(q, rss, x) : List<&2, B.Ru>}:
  Equal.trans(List<&2, B.Ru>, B.uses.of(List.reverse.go(&2, U32, r, Con{x, q}), rss, x), B.uses.of(Con{x, q}, rss, x), B.uses.of(q, rss, x),
    rev_none(r, Con{x, q}, rss, x, r, ordered_closed(r, B.calls(rss), MB.eq_true_of_and_right(B.all.in(B.ids.at(B.calls(rss), x), r), B.ordered(r, B.calls(rss)), h1)),
      not_true(B.has(r, x), MB.eq_true_of_and_left(Bool.not(B.has(r, x)), B.distinct(r), h2))),
    Equal.cong(List<&2, B.Ru>, List<&2, B.Ru>, z => List.append(&2, B.Ru, z, B.uses.of(q, rss, x)), B.uses.in(B.rus.at(rss, x), x, x), Nil{},
      use_none(rss, x, x, r, MB.eq_true_of_and_left(B.all.in(B.ids.at(B.calls(rss), x), r), B.ordered(r, B.calls(rss)), h1),
        not_true(B.has(r, x), MB.eq_true_of_and_left(Bool.not(B.has(r, x)), B.distinct(r), h2)))))

# mults from the units q taken equals the specification, the order the
# rest reversed onto q
def disp(rest: List<&2, U32>, +q: List<&2, U32>, +rss: List<&2, List<&2, B.Ru>>, +ut: B.Ht<B.Un>, +obs: List<&2, B.Ob>, +us: List<&2, B.Un>, s: B.Ms,
    +h1: {B.ordered(rest, B.calls(rss)) == True{} : Bool}, +h2: {B.distinct(rest) == True{} : Bool}) ->
    {B.mults(rest, B.pw.of(List<&2, B.Ru>, rss), ut, obs, us, s, pa(q, B.pw.of(List<&2, B.Ru>, rss))) == B.mults.spec(rest, List.reverse.go(&2, U32, rest, q), rss, ut, obs, us, s) : B.Ms}:
  match rest:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      %Equal.sym(List<&2, B.Ru>, B.pend.at(pa(q, B.pw.of(List<&2, B.Ru>, rss)), x), B.uses.of(q, rss, x), pa_at(q, rss, x)) :
        {B.mults(r, B.pw.of(List<&2, B.Ru>, rss), ut, obs, us, B.mult.of(x, B.mult.share(x, ut), _, obs, us, ut, s), pa(Con{x, q}, B.pw.of(List<&2, B.Ru>, rss))) ==
          B.mults.spec(r, List.reverse.go(&2, U32, r, Con{x, q}), rss, ut, obs, us,
            B.mult.of(x, B.mult.share(x, ut), B.uses.of(List.reverse.go(&2, U32, r, Con{x, q}), rss, x), obs, us, ut, s)) : B.Ms}
      %Equal.sym(List<&2, B.Ru>, B.uses.of(List.reverse.go(&2, U32, r, Con{x, q}), rss, x), B.uses.of(q, rss, x), at_turn(x, r, q, rss, h1, h2)) :
        {B.mults(r, B.pw.of(List<&2, B.Ru>, rss), ut, obs, us, B.mult.of(x, B.mult.share(x, ut), B.uses.of(q, rss, x), obs, us, ut, s), pa(Con{x, q}, B.pw.of(List<&2, B.Ru>, rss))) ==
          B.mults.spec(r, List.reverse.go(&2, U32, r, Con{x, q}), rss, ut, obs, us,
            B.mult.of(x, B.mult.share(x, ut), _, obs, us, ut, s)) : B.Ms}
      disp(r, Con{x, q}, rss, ut, obs, us, B.mult.of(x, B.mult.share(x, ut), B.uses.of(q, rss, x), obs, us, ut, s),
        MB.eq_true_of_and_right(B.all.in(B.ids.at(B.calls(rss), x), r), B.ordered(r, B.calls(rss)), h1),
        MB.eq_true_of_and_right(Bool.not(B.has(r, x)), B.distinct(r), h2))

def Laws.mults.uses(xs, rss, ut, obs, us, s, h1, h2):
  disp(xs, Nil{}, rss, ut, obs, us, s, h1, h2)

def Laws.mults.walked(roots, rss, ut, obs, us, s):
  %Equal.sym(B.Ds, B.df.ds(B.walk.fast(roots, B.calls(rss), obs, us)), B.walk(roots, B.calls(rss), obs, us), Laws.order.fast(roots, B.calls(rss), obs, us)) :
    {B.mults(B.ds.order(_), B.pw.of(List<&2, B.Ru>, rss), ut, obs, us, s, B.WmNone{}) ==
      B.mults.spec(B.ds.order(_), List.reverse(&2, U32, B.ds.order(_)), rss, ut, obs, us, s) : B.Ms}
  Laws.mults.uses(B.ds.order(B.walk(roots, B.calls(rss), obs, us)), rss, ut, obs, us, s,
    Laws.order.callees_first(roots, B.calls(rss), obs, us), Laws.order.once(roots, B.calls(rss), obs, us))

# Names emitted once
# ------------------
#
# The names check keeps the names seen in a hash trie: a name put is
# found again at its own hash (`leaf_put`), and a put elsewhere loses no
# name (`seen_mono`), so that where it reports none, no name follows one
# the same (`no_repeat`), and the names are distinct (`distinct_of`).

# a hash's next bit and the rest
def nb(+h: U32) -> U32:
  ((h >> 1n : U32) .&. 1 : U32)

def nh(+h: U32) -> U32:
  (h >> 1n : U32)

def leaf_put.k(-A: Data, c: Bool, +k: Nat, +z: B.Ht<A>, +o: B.Ht<A>, +b: U32, +h: U32, +e: A, eq: {c == U32.is_eq(b, 0) : Bool},
    ih: @s:B.Ht<A> -> {Con{e, B.ht.leaf.go(A, k, s, nb(h), nh(h))} == B.ht.leaf.go(A, k, B.ht.put.go(A, k, s, nb(h), nh(h), e), nb(h), nh(h)) : List<&2, A>}) ->
    {Con{e, B.ht.leaf.go(A, 1n+k, B.HNode{z, o}, b, h)} ==
      B.ht.leaf.go(A, 1n+k, B.ht.join(A, c, B.ht.put.go(A, k, B.ht.pick(A, c, z, o), nb(h), nh(h), e), B.ht.pick(A, c, o, z)), b, h) : List<&2, A>}:
  match c:
    case True{}:
      %eq : {Con{e, B.ht.leaf.go(A, k, B.ht.pick(A, _, z, o), nb(h), nh(h))} ==
        B.ht.leaf.go(A, k, B.ht.pick(A, _, B.ht.put.go(A, k, z, nb(h), nh(h), e), o), nb(h), nh(h)) : List<&2, A>}
      ih(z)
    case False{}:
      %eq : {Con{e, B.ht.leaf.go(A, k, B.ht.pick(A, _, z, o), nb(h), nh(h))} ==
        B.ht.leaf.go(A, k, B.ht.pick(A, _, z, B.ht.put.go(A, k, o, nb(h), nh(h), e)), nb(h), nh(h)) : List<&2, A>}
      ih(o)

# an entry put is first in the leaf of its own hash
def leaf_put(-A: Data, fuel: Nat, t: B.Ht<A>, +b: U32, +h: U32, +e: A) ->
    {Con{e, B.ht.leaf.go(A, fuel, t, b, h)} == B.ht.leaf.go(A, fuel, B.ht.put.go(A, fuel, t, b, h, e), b, h) : List<&2, A>}:
  match fuel:
    case 0n:
      match t:
        case B.HLeaf{es}:
          {==}
        case B.HNode{z, o}:
          {==}
    case 1n+(+k):
      match t:
        case B.HLeaf{es}:
          {==}
        case B.HNode{+z, +o}:
          leaf_put.k(A, U32.is_eq(b, 0), k, z, o, b, h, e, {==}, s => leaf_put(A, k, s, nb(h), nh(h), e))

# a name found in a list of names, nm.find's step mirrored
def has_n(l: List<&2, B.Nm>, +n: List<&2, U32>) -> Bool:
  Maybe.is_some(&2, U32, B.nm.find(l, n))

def find_k(+sm: Bool, +no: U32, l: List<&2, B.Nm>, +n: List<&2, U32>) -> Maybe<&2, U32>:
  B.when(Maybe<&2, U32>, sm, v => Some{no}, v => B.nm.find(l, n))

def find_cons.k(sm: Bool, +no: U32, l: List<&2, B.Nm>, +n: List<&2, U32>, hs: {has_n(l, n) == True{} : Bool}) ->
    {Maybe.is_some(&2, U32, find_k(sm, no, l, n)) == True{} : Bool}:
  match sm:
    case True{}:
      {==}
    case False{}:
      hs

# a name found stays found with a name before it
def find_cons(m: B.Nm, l: List<&2, B.Nm>, +n: List<&2, U32>, hs: {has_n(l, n) == True{} : Bool}) -> {has_n(Con{m, l}, n) == True{} : Bool}:
  match m:
    case B.Nm{+name, +u, +no}:
      find_cons.k(B.same(name, n), no, l, n, hs)

# a name first is found
def find_self(+name: List<&2, U32>, +u: U32, +no: U32, l: List<&2, B.Nm>) -> {has_n(Con{B.Nm{name, u, no}, l}, name) == True{} : Bool}:
  %Equal.sym(Bool, B.same(name, name), True{}, Laws.names.same_refl(name)) : {Maybe.is_some(&2, U32, find_k(_, no, l, name)) == True{} : Bool}
  {==}

def mono.k(c2: Bool, c: Bool, +k: Nat, +z: B.Ht<B.Nm>, +o: B.Ht<B.Nm>, +b: U32, +h: U32, +h2: U32, +m: B.Nm, +n: List<&2, U32>,
    eq: {c == U32.is_eq(b, 0) : Bool},
    hs: {has_n(B.ht.leaf.go(B.Nm, k, B.ht.pick(B.Nm, c, z, o), nb(h), nh(h)), n) == True{} : Bool},
    ih: @s:B.Ht<B.Nm> -> @hs2:{has_n(B.ht.leaf.go(B.Nm, k, s, nb(h), nh(h)), n) == True{} : Bool} ->
      {has_n(B.ht.leaf.go(B.Nm, k, B.ht.put.go(B.Nm, k, s, nb(h2), nh(h2), m), nb(h), nh(h)), n) == True{} : Bool}) ->
    {has_n(B.ht.leaf.go(B.Nm, 1n+k, B.ht.join(B.Nm, c2, B.ht.put.go(B.Nm, k, B.ht.pick(B.Nm, c2, z, o), nb(h2), nh(h2), m), B.ht.pick(B.Nm, c2, o, z)), b, h), n) == True{} : Bool}:
  match c2 c:
    case True{} True{}:
      %eq : {has_n(B.ht.leaf.go(B.Nm, k, B.ht.pick(B.Nm, _, B.ht.put.go(B.Nm, k, z, nb(h2), nh(h2), m), o), nb(h), nh(h)), n) == True{} : Bool}
      ih(z, hs)
    case True{} False{}:
      %eq : {has_n(B.ht.leaf.go(B.Nm, k, B.ht.pick(B.Nm, _, B.ht.put.go(B.Nm, k, z, nb(h2), nh(h2), m), o), nb(h), nh(h)), n) == True{} : Bool}
      hs
    case False{} True{}:
      %eq : {has_n(B.ht.leaf.go(B.Nm, k, B.ht.pick(B.Nm, _, z, B.ht.put.go(B.Nm, k, o, nb(h2), nh(h2), m)), nb(h), nh(h)), n) == True{} : Bool}
      hs
    case False{} False{}:
      %eq : {has_n(B.ht.leaf.go(B.Nm, k, B.ht.pick(B.Nm, _, z, B.ht.put.go(B.Nm, k, o, nb(h2), nh(h2), m)), nb(h), nh(h)), n) == True{} : Bool}
      ih(o, hs)

# a name found in the leaf of its hash stays found, whatever is put
def seen_mono(fuel: Nat, t: B.Ht<B.Nm>, +b: U32, +h: U32, +b2: U32, +h2: U32, +m: B.Nm, +n: List<&2, U32>,
    hs: {has_n(B.ht.leaf.go(B.Nm, fuel, t, b, h), n) == True{} : Bool}) ->
    {has_n(B.ht.leaf.go(B.Nm, fuel, B.ht.put.go(B.Nm, fuel, t, b2, h2, m), b, h), n) == True{} : Bool}:
  match fuel:
    case 0n:
      match t:
        case B.HLeaf{es}:
          find_cons(m, es, n, hs)
        case B.HNode{z, o}:
          Empty.absurd({has_n(Con{m, Nil{}}, n) == True{} : Bool}, MB.false_ne_true()(hs))
    case 1n+(+k):
      match t:
        case B.HLeaf{es}:
          find_cons(m, es, n, hs)
        case B.HNode{+z, +o}:
          mono.k(U32.is_eq(b2, 0), U32.is_eq(b, 0), k, z, o, b, h, h2, m, n, {==}, hs,
            s => hs2 => seen_mono(k, s, nb(h), nh(h), nb(h2), nh(h2), m, n, hs2))

# the names check's trie: a name put is seen, and a name seen stays seen
def seen_put(+t: B.Ht<B.Nm>, +name: List<&2, U32>, +u: U32, +no: U32) ->
    {Maybe.is_some(&2, U32, B.nm.seen(B.nm.put(t, B.Nm{name, u, no}), name)) == True{} : Bool}:
  %leaf_put(B.Nm, 32n, t, (B.hash.name(name) .&. 1 : U32), B.hash.name(name), B.Nm{name, u, no}) : {has_n(_, name) == True{} : Bool}
  find_self(name, u, no, B.ht.leaf.go(B.Nm, 32n, t, (B.hash.name(name) .&. 1 : U32), B.hash.name(name)))

def nm_mono(+t: B.Ht<B.Nm>, m: B.Nm, +n: List<&2, U32>, hs: {Maybe.is_some(&2, U32, B.nm.seen(t, n)) == True{} : Bool}) ->
    {Maybe.is_some(&2, U32, B.nm.seen(B.nm.put(t, m), n)) == True{} : Bool}:
  match m:
    case B.Nm{+name, +u, +no}:
      seen_mono(32n, t, (B.hash.name(n) .&. 1 : U32), B.hash.name(n), (B.hash.name(name) .&. 1 : U32), B.hash.name(name), B.Nm{name, u, no}, n, hs)

# the names check's step mirrored: a name seen before an error, else the
# name kept for those after it
def ers_k(+mb: Maybe<&2, U32>, +name: List<&2, U32>, +u: U32, +no: U32, +t: List<&2, B.Nm>, +seen: B.Ht<B.Nm>) -> List<&2, B.Er>:
  B.on.maybe(U32, List<&2, B.Er>, mb, v => B.er.names(t, B.nm.put(seen, B.Nm{name, u, no})),
    +l => Con{B.Er{no, B.text(name) ++ " would name two emitted definitions, those of lines " ++ U32.show(l) ++ " and " ++
      U32.show(no) ++ ": rename one"}, B.er.names(t, B.nm.put(seen, B.Nm{name, u, no}))})

def nil_disc(-A: Data, xs: List<&2, A>) -> Type:
  match xs:
    case Nil{}:
      Unit
    case Con{c, cs}:
      Empty

def ers_some(+l: U32, +name: List<&2, U32>, +u: U32, +no: U32, +t: List<&2, B.Nm>, +seen: B.Ht<B.Nm>,
    hn: {ers_k(Some{l}, name, u, no, t, seen) == Nil{} : List<&2, B.Er>}) -> Empty:
  %Equal.sym(List<&2, B.Er>, ers_k(Some{l}, name, u, no, t, seen), Nil{}, hn) : nil_disc(B.Er, _)
  Unit{}

# where the check reports none, the name was not seen before, and the
# rest report none with it seen
def seen_none(mb: Maybe<&2, U32>, +name: List<&2, U32>, +u: U32, +no: U32, +t: List<&2, B.Nm>, +seen: B.Ht<B.Nm>,
    hn: {ers_k(mb, name, u, no, t, seen) == Nil{} : List<&2, B.Er>}) -> {Maybe.is_some(&2, U32, mb) == False{} : Bool}:
  match mb:
    case None{}:
      {==}
    case Some{+l}:
      Empty.absurd({True{} == False{} : Bool}, ers_some(l, name, u, no, t, seen, hn))

def rest_nil(mb: Maybe<&2, U32>, +name: List<&2, U32>, +u: U32, +no: U32, +t: List<&2, B.Nm>, +seen: B.Ht<B.Nm>,
    hn: {ers_k(mb, name, u, no, t, seen) == Nil{} : List<&2, B.Er>}) -> {B.er.names(t, B.nm.put(seen, B.Nm{name, u, no})) == Nil{} : List<&2, B.Er>}:
  match mb:
    case None{}:
      hn
    case Some{+l}:
      Empty.absurd({B.er.names(t, B.nm.put(seen, B.Nm{name, u, no})) == Nil{} : List<&2, B.Er>}, ers_some(l, name, u, no, t, seen, hn))

# a name seen, and one unseen the same as it: none
def clash(+s: B.Ht<B.Nm>, +name: List<&2, U32>, +n: List<&2, U32>, e: {name == n : List<&2, U32>},
    h1: {Maybe.is_some(&2, U32, B.nm.seen(s, name)) == False{} : Bool}) -> {False{} == Maybe.is_some(&2, U32, B.nm.seen(s, n)) : Bool}:
  %e : {False{} == Maybe.is_some(&2, U32, B.nm.seen(s, _)) : Bool}
  Equal.sym(Bool, Maybe.is_some(&2, U32, B.nm.seen(s, name)), False{}, h1)

def no_repeat.k(sm: Bool, +name: List<&2, U32>, +n: List<&2, U32>, +no: U32, +t: List<&2, B.Nm>, +s: B.Ht<B.Nm>,
    eq: {sm == B.same(name, n) : Bool},
    hnone: {Maybe.is_some(&2, U32, B.nm.seen(s, name)) == False{} : Bool},
    hs: {Maybe.is_some(&2, U32, B.nm.seen(s, n)) == True{} : Bool},
    ih: {has_n(t, n) == False{} : Bool}) ->
    {Maybe.is_some(&2, U32, find_k(sm, no, t, n)) == False{} : Bool}:
  match sm:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, MB.false_ne_true()(Equal.trans(Bool, False{}, Maybe.is_some(&2, U32, B.nm.seen(s, n)), True{},
        clash(s, name, n, Laws.names.same_eq(name, n, Equal.sym(Bool, True{}, B.same(name, n), eq)), hnone), hs)))
    case False{}:
      ih

# where the check reports none, no name it reads was seen before it
def no_repeat(t: List<&2, B.Nm>, +s: B.Ht<B.Nm>, +n: List<&2, U32>, +hn: {B.er.names(t, s) == Nil{} : List<&2, B.Er>},
    +hs: {Maybe.is_some(&2, U32, B.nm.seen(s, n)) == True{} : Bool}) -> {has_n(t, n) == False{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case Con{m, +t2}:
      match m:
        case B.Nm{+name, +u, +no}:
          no_repeat.k(B.same(name, n), name, n, no, t2, s, {==}, seen_none(B.nm.seen(s, name), name, u, no, t2, s, hn), hs,
            no_repeat(t2, B.nm.put(s, B.Nm{name, u, no}), n, rest_nil(B.nm.seen(s, name), name, u, no, t2, s, hn), nm_mono(s, B.Nm{name, u, no}, n, hs)))

# so where it reports none, the names are distinct
def distinct_of(ns: List<&2, B.Nm>, +s: B.Ht<B.Nm>, +hn: {B.er.names(ns, s) == Nil{} : List<&2, B.Er>}) -> {B.nms.distinct(ns) == True{} : Bool}:
  match ns:
    case Nil{}:
      {==}
    case Con{m, +t}:
      match m:
        case B.Nm{+name, +u, +no}:
          %Equal.sym(Bool, has_n(t, name), False{}, no_repeat(t, B.nm.put(s, B.Nm{name, u, no}), name, rest_nil(B.nm.seen(s, name), name, u, no, t, s, hn), seen_put(s, name, u, no))) :
            {Bool.and(Bool.not(_), B.nms.distinct(t)) == True{} : Bool}
          distinct_of(t, B.nm.put(s, B.Nm{name, u, no}), rest_nil(B.nm.seen(s, name), name, u, no, t, s, hn))

def Laws.emit.unique(xs, e, h):
  %Laws.emit.names(xs, e) : {B.nms.distinct(_) == True{} : Bool}
  distinct_of(B.names.all(xs, e), B.ht.for(B.Nm, List.length(&2, B.Nm, B.names.all(xs, e))), h)

# C3
# --
#
# The merge, run with an accumulator, is its direct recursion
# (`mrest`) with the order taken so far before it (`merge_acc`). A
# merge that succeeds keeps every list, as each turn takes heads, and
# holds each object once, as one taken is in no tail and leaves every
# list (`mrest_sound`). Given an order keeping every list and holding
# each object once, a free head exists, the order's first object any
# list holds being in no tail (`good_of`), so that the merge never fails
# before its fuel, the lists' lengths, is spent (`merge_ok`).

def first_mg(+id: U32, m: B.Mg) -> {List.head(&2, U32, B.lz.ord(Some{B.lin.mg(id, m)})) == Some{id} : Maybe<&2, U32>}:
  match m:
    case B.MOk{ord}:
      {==}
    case B.MFail{ss}:
      {==}

def Laws.c3.first(id, ps, ss):
  match ss:
    case None{}:
      {==}
    case Some{+seqs}:
      first_mg(id, B.c3.merge(1n+B.sqs.len(List.append(&2, B.Sq, seqs, [B.Sq{id, ps}])), B.c3.take(List.append(&2, B.Sq, seqs, [B.Sq{id, ps}]), 4294967295), Nil{}))

# the merge without its accumulator, an object taken put before the rest
def mcons(+g: U32, m: B.Mg) -> B.Mg:
  match m:
    case B.MOk{ord}:
      B.MOk{Con{g, ord}}
    case B.MFail{ss}:
      B.MFail{ss}

def mrest(n: Nat, +seqs: List<&2, B.Sq>) -> B.Mg:
  match n:
    case 0n:
      B.MFail{seqs}
    case 1n+k:
      match seqs:
        case Nil{}:
          B.MOk{Nil{}}
        case Con{+s, +t}:
          B.on.maybe(U32, B.Mg, B.c3.good(Con{s, t}, Con{s, t}), u => B.MFail{Con{s, t}}, +h => mcons(h, mrest(k, B.c3.take(Con{s, t}, h))))

def mrest_k(+mb: Maybe<&2, U32>, +k: Nat, +s: B.Sq, +t: List<&2, B.Sq>) -> B.Mg:
  B.on.maybe(U32, B.Mg, mb, u => B.MFail{Con{s, t}}, +h => mcons(h, mrest(k, B.c3.take(Con{s, t}, h))))

def merge_k(+mb: Maybe<&2, U32>, +k: Nat, +s: B.Sq, +t: List<&2, B.Sq>, +out: List<&2, U32>) -> B.Mg:
  B.on.maybe(U32, B.Mg, mb, u => B.MFail{Con{s, t}}, +h => B.c3.merge(k, B.c3.take(Con{s, t}, h), Con{h, out}))

# an order with a prefix before it
def mpre(+p: List<&2, U32>, m: B.Mg) -> B.Mg:
  match m:
    case B.MOk{ord}:
      B.MOk{List.append(&2, U32, p, ord)}
    case B.MFail{ss}:
      B.MFail{ss}

def mpre_nil(m: B.Mg) -> {m == mpre(Nil{}, m) : B.Mg}:
  match m:
    case B.MOk{ord}:
      {==}
    case B.MFail{ss}:
      {==}

def pre_cons(+p: List<&2, U32>, +h: U32, m: B.Mg) -> {mpre(p, mcons(h, m)) == mpre(List.append(&2, U32, p, [h]), m) : B.Mg}:
  match m:
    case B.MOk{+o}:
      %assoc_r(p, [h], o) : {B.MOk{List.append(&2, U32, p, Con{h, o})} == B.MOk{_} : B.Mg}
      {==}
    case B.MFail{ss}:
      {==}

def acc_k(mb: Maybe<&2, U32>, +k: Nat, +s: B.Sq, +t: List<&2, B.Sq>, +out: List<&2, U32>,
    ih: @h:U32 -> {mpre(List.reverse(&2, U32, Con{h, out}), mrest(k, B.c3.take(Con{s, t}, h))) == B.c3.merge(k, B.c3.take(Con{s, t}, h), Con{h, out}) : B.Mg}) ->
    {mpre(List.reverse(&2, U32, out), mrest_k(mb, k, s, t)) == merge_k(mb, k, s, t, out) : B.Mg}:
  match mb:
    case None{}:
      {==}
    case Some{+h}:
      %ih(h) : {mpre(List.reverse(&2, U32, out), mcons(h, mrest(k, B.c3.take(Con{s, t}, h)))) == _ : B.Mg}
      %rev_snoc(out, h) : {mpre(List.reverse(&2, U32, out), mcons(h, mrest(k, B.c3.take(Con{s, t}, h)))) == mpre(_, mrest(k, B.c3.take(Con{s, t}, h))) : B.Mg}
      pre_cons(List.reverse(&2, U32, out), h, mrest(k, B.c3.take(Con{s, t}, h)))

# the merge is its direct recursion after the order taken so far
def merge_acc(n: Nat, +seqs: List<&2, B.Sq>, +out: List<&2, U32>) ->
    {mpre(List.reverse(&2, U32, out), mrest(n, seqs)) == B.c3.merge(n, seqs, out) : B.Mg}:
  match n:
    case 0n:
      {==}
    case 1n+(+k):
      match seqs:
        case Nil{}:
          %ML.append_nil_sym(&2, U32, List.reverse(&2, U32, out)) : {B.MOk{_} == B.MOk{List.reverse(&2, U32, out)} : B.Mg}
          {==}
        case Con{+s, +t}:
          acc_k(B.c3.good(Con{s, t}, Con{s, t}), k, s, t, out, +h => merge_acc(k, B.c3.take(Con{s, t}, h), Con{h, out}))

# Bools
def and_l(+a: Bool, +b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, MB.false_ne_true()(h))

def and_r(+a: Bool, +b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      Empty.absurd({b == True{} : Bool}, MB.false_ne_true()(h))

def or_l_true(+a: Bool, +b: Bool, h: {a == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, h) : {Bool.or(_, b) == True{} : Bool}
  {==}

def or_r_true(+a: Bool, +b: Bool, h: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h

def not_false(+b: Bool, h: {b == False{} : Bool}) -> {Bool.not(b) == True{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({False{} == True{} : Bool}, MB.true_ne_false()(h))
    case False{}:
      {==}

# a Bool both: none
def both(+b: Bool, ht: {b == True{} : Bool}, hf: {b == False{} : Bool}) -> Empty:
  MB.false_ne_true()(Equal.trans(Bool, False{}, b, True{}, Equal.sym(Bool, b, False{}, hf), ht))

def mget(m: Maybe<&2, U32>) -> U32:
  match m:
    case None{}:
      0
    case Some{+x}:
      x

def some_inj(+g: U32, +h: U32, e: {Some{g} == Some{h} : Maybe<&2, U32>}) -> {g == h : U32}:
  %e : {g == mget(_) : U32}
  {==}

def maybe_disc(m: Maybe<&2, U32>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      Empty

def some_none(+g: U32, e: {Some{g} == None{} : Maybe<&2, U32>}) -> Empty:
  %Equal.sym(Maybe<&2, U32>, Some{g}, None{}, e) : maybe_disc(_)
  Unit{}

# the lists' objects; each of xs among them; a head of one
def sqs.has(ss: List<&2, B.Sq>, +x: U32) -> Bool:
  match ss:
    case Nil{}:
      False{}
    case Con{s, t}:
      match s:
        case B.Sq{+o, xs}:
          Bool.or(B.has(xs, x), sqs.has(t, x))

def sqs.all(xs: List<&2, U32>, +ss: List<&2, B.Sq>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, t}:
      Bool.and(sqs.has(ss, x), sqs.all(t, ss))

def is.head(ss: List<&2, B.Sq>, +y: U32) -> Bool:
  match ss:
    case Nil{}:
      False{}
    case Con{s, t}:
      match s:
        case B.Sq{+o, xs}:
          match xs:
            case Nil{}:
              is.head(t, y)
            case Con{+x, r}:
              Bool.or(U32.is_eq(x, y), is.head(t, y))

# a merge's order keeps every list, holds each object once, and only
# objects the lists hold
def minv(m: B.Mg, +ss: List<&2, B.Sq>) -> Bool:
  match m:
    case B.MOk{+ord}:
      Bool.and(B.sqs.kept(ss, ord), Bool.and(B.distinct(ord), sqs.all(ord, ss)))
    case B.MFail{x}:
      True{}

# c3.head.drop's and subseq's steps mirrored
def dk(+b: Bool, +x: U32, +r: List<&2, U32>) -> List<&2, U32>:
  B.when(List<&2, U32>, b, u => r, u => Con{x, r})

def sub_k(+b: Bool, +yr: List<&2, U32>, +x: U32, +r: List<&2, U32>) -> Bool:
  B.when(Bool, b, u => B.subseq(yr, r), u => B.subseq(yr, Con{x, r}))

def sub_nil(ys: List<&2, U32>) -> {B.subseq(ys, Nil{}) == True{} : Bool}:
  match ys:
    case Nil{}:
      {==}
    case Con{y, yr}:
      {==}

def drop_sub.k(b: Bool, +x: U32, +r: List<&2, U32>, +g: U32, +o: List<&2, U32>, eq: {b == U32.is_eq(x, g) : Bool},
    hk: {B.subseq(o, dk(b, x, r)) == True{} : Bool}) -> {B.subseq(Con{g, o}, Con{x, r}) == True{} : Bool}:
  match b:
    case True{}:
      %eq : {sub_k(_, o, x, r) == True{} : Bool}
      hk
    case False{}:
      %eq : {sub_k(_, o, x, r) == True{} : Bool}
      hk

# a list whose rest an order keeps, the object taken before that order
def drop_sub(xs: List<&2, U32>, +g: U32, +o: List<&2, U32>, hk: {B.subseq(o, B.c3.head.drop(xs, g)) == True{} : Bool}) ->
    {B.subseq(Con{g, o}, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      drop_sub.k(U32.is_eq(x, g), x, r, g, o, {==}, hk)

def keep_kept(+o: U32, d: List<&2, U32>, +t: List<&2, B.Sq>, +ys: List<&2, U32>, hk: {B.sqs.kept(B.c3.keep(o, d, t), ys) == True{} : Bool}) ->
    {B.subseq(ys, d) == True{} : Bool}:
  match d:
    case Nil{}:
      sub_nil(ys)
    case Con{+x, +r}:
      and_l(B.subseq(ys, Con{x, r}), B.sqs.kept(t, ys), hk)

def keep_kept_t(+o: U32, d: List<&2, U32>, +t: List<&2, B.Sq>, +ys: List<&2, U32>, hk: {B.sqs.kept(B.c3.keep(o, d, t), ys) == True{} : Bool}) ->
    {B.sqs.kept(t, ys) == True{} : Bool}:
  match d:
    case Nil{}:
      hk
    case Con{+x, +r}:
      and_r(B.subseq(ys, Con{x, r}), B.sqs.kept(t, ys), hk)

# the lists kept by the order after an object, the object taken from
# their heads: they are kept by the object then that order
def kept_cons(ss: List<&2, B.Sq>, +g: U32, +o: List<&2, U32>, +hk: {B.sqs.kept(B.c3.take(ss, g), o) == True{} : Bool}) ->
    {B.sqs.kept(ss, Con{g, o}) == True{} : Bool}:
  match ss:
    case Nil{}:
      {==}
    case Con{s, +t}:
      match s:
        case B.Sq{+so, +xs}:
          and_intro(B.subseq(Con{g, o}, xs), B.sqs.kept(t, Con{g, o}),
            drop_sub(xs, g, o, keep_kept(so, B.c3.head.drop(xs, g), B.c3.take(t, g), o, hk)),
            kept_cons(t, g, o, keep_kept_t(so, B.c3.head.drop(xs, g), B.c3.take(t, g), o, hk)))

# a disjunction's sides each implying another's
def or_map(+a: Bool, +b: Bool, +c: Bool, +d: Bool, h: {Bool.or(a, b) == True{} : Bool},
    f: {a == True{} : Bool} -> {c == True{} : Bool}, g: {b == True{} : Bool} -> {d == True{} : Bool}) -> {Bool.or(c, d) == True{} : Bool}:
  match a:
    case True{}:
      or_l_true(c, d, f({==}))
    case False{}:
      or_r_true(c, d, g(h))

def drop_has.k(b: Bool, +y: U32, +r: List<&2, U32>, +x: U32, h: {B.has(dk(b, y, r), x) == True{} : Bool}) ->
    {B.has(Con{y, r}, x) == True{} : Bool}:
  match b:
    case True{}:
      or_r_true(U32.is_eq(y, x), B.has(r, x), h)
    case False{}:
      h

def drop_has(xs: List<&2, U32>, +g: U32, +x: U32, h: {B.has(B.c3.head.drop(xs, g), x) == True{} : Bool}) -> {B.has(xs, x) == True{} : Bool}:
  match xs:
    case Nil{}:
      h
    case Con{+y, +r}:
      drop_has.k(U32.is_eq(y, g), y, r, x, h)

def keep_has(+o: U32, d: List<&2, U32>, +t: List<&2, B.Sq>, +x: U32, h: {sqs.has(B.c3.keep(o, d, t), x) == True{} : Bool}) ->
    {Bool.or(B.has(d, x), sqs.has(t, x)) == True{} : Bool}:
  match d:
    case Nil{}:
      h
    case Con{+y, +r}:
      h

# an object the lists hold after a take, they held before
def take_has(ss: List<&2, B.Sq>, +g: U32, +x: U32, h: {sqs.has(B.c3.take(ss, g), x) == True{} : Bool}) -> {sqs.has(ss, x) == True{} : Bool}:
  match ss:
    case Nil{}:
      h
    case Con{s, +t}:
      match s:
        case B.Sq{+o, +xs}:
          or_map(B.has(B.c3.head.drop(xs, g), x), sqs.has(B.c3.take(t, g), x), B.has(xs, x), sqs.has(t, x),
            keep_has(o, B.c3.head.drop(xs, g), B.c3.take(t, g), x, h),
            p => drop_has(xs, g, x, p), q => take_has(t, g, x, q))

def keep_has_f(+o: U32, d: List<&2, U32>, +t: List<&2, B.Sq>, +x: U32, hd: {B.has(d, x) == False{} : Bool}, ht: {sqs.has(t, x) == False{} : Bool}) ->
    {sqs.has(B.c3.keep(o, d, t), x) == False{} : Bool}:
  match d:
    case Nil{}:
      ht
    case Con{+y, +r}:
      %Equal.sym(Bool, B.has(Con{y, r}, x), False{}, hd) : {Bool.or(_, sqs.has(t, x)) == False{} : Bool}
      ht

def gone_k(b: Bool, +x: U32, +r: List<&2, U32>, +g: U32, eq: {b == U32.is_eq(x, g) : Bool}, hr: {B.has(r, g) == False{} : Bool}) ->
    {B.has(dk(b, x, r), g) == False{} : Bool}:
  match b:
    case True{}:
      hr
    case False{}:
      %eq : {Bool.or(_, B.has(r, g)) == False{} : Bool}
      hr

# an object in no tail, taken from the heads, is in no list
def take_gone(ss: List<&2, B.Sq>, +g: U32, +ht: {B.in_tails(ss, g) == False{} : Bool}) -> {sqs.has(B.c3.take(ss, g), g) == False{} : Bool}:
  match ss:
    case Nil{}:
      {==}
    case Con{s, +t}:
      match s:
        case B.Sq{+o, xs}:
          match xs:
            case Nil{}:
              take_gone(t, g, ht)
            case Con{+x, +r}:
              keep_has_f(o, dk(U32.is_eq(x, g), x, r), B.c3.take(t, g), g,
                gone_k(U32.is_eq(x, g), x, r, g, {==}, or_false_l(B.has(r, g), B.in_tails(t, g), ht)),
                take_gone(t, g, or_false_r(B.has(r, g), B.in_tails(t, g), ht)))

def has_eq(+t: List<&2, B.Sq>, +x: U32, +g: U32, e: {x == g : U32}, hn: {sqs.has(t, g) == False{} : Bool}) -> {sqs.has(t, x) == False{} : Bool}:
  %Equal.sym(U32, x, g, e) : {sqs.has(t, _) == False{} : Bool}
  hn

def all_not.k(b: Bool, +x: U32, +r: List<&2, U32>, +g: U32, +t: List<&2, B.Sq>, eq: {b == U32.is_eq(x, g) : Bool},
    hx: {sqs.has(t, x) == True{} : Bool}, hn: {sqs.has(t, g) == False{} : Bool}, ih: {B.has(r, g) == False{} : Bool}) ->
    {Bool.or(U32.is_eq(x, g), B.has(r, g)) == False{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({Bool.or(U32.is_eq(x, g), B.has(r, g)) == False{} : Bool},
        both(sqs.has(t, x), hx, has_eq(t, x, g, u32_eq_of_is_eq(x, g, Equal.sym(Bool, True{}, U32.is_eq(x, g), eq)), hn)))
    case False{}:
      %eq : {Bool.or(_, B.has(r, g)) == False{} : Bool}
      ih

# an order of objects the lists hold has none they lack
def all_not(o: List<&2, U32>, +t: List<&2, B.Sq>, +g: U32, +ha: {sqs.all(o, t) == True{} : Bool}, +hn: {sqs.has(t, g) == False{} : Bool}) ->
    {B.has(o, g) == False{} : Bool}:
  match o:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      all_not.k(U32.is_eq(x, g), x, r, g, t, {==}, and_l(sqs.has(t, x), sqs.all(r, t), ha), hn,
        all_not(r, t, g, and_r(sqs.has(t, x), sqs.all(r, t), ha), hn))

def all_take(o: List<&2, U32>, +ss: List<&2, B.Sq>, +g: U32, +h: {sqs.all(o, B.c3.take(ss, g)) == True{} : Bool}) -> {sqs.all(o, ss) == True{} : Bool}:
  match o:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      and_intro(sqs.has(ss, x), sqs.all(r, ss), take_has(ss, g, x, and_l(sqs.has(B.c3.take(ss, g), x), sqs.all(r, B.c3.take(ss, g)), h)),
        all_take(r, ss, g, and_r(sqs.has(B.c3.take(ss, g), x), sqs.all(r, B.c3.take(ss, g)), h)))

def head_has(ss: List<&2, B.Sq>, +g: U32, +h: {is.head(ss, g) == True{} : Bool}) -> {sqs.has(ss, g) == True{} : Bool}:
  match ss:
    case Nil{}:
      h
    case Con{s, +t}:
      match s:
        case B.Sq{+o, xs}:
          match xs:
            case Nil{}:
              head_has(t, g, h)
            case Con{+x, +r}:
              or_map(U32.is_eq(x, g), is.head(t, g), B.has(Con{x, r}, g), sqs.has(t, g), h,
                p => or_l_true(U32.is_eq(x, g), B.has(r, g), p), q => head_has(t, g, q))

# c3.good's step mirrored: the head found is a head, and in no tail
def gk(+b: Bool, +h: U32, +t: List<&2, B.Sq>, +all: List<&2, B.Sq>) -> Maybe<&2, U32>:
  B.when(Maybe<&2, U32>, b, u => B.c3.good(t, all), u => Some{h})

def good_head.k(b: Bool, +h: U32, +t: List<&2, B.Sq>, +all: List<&2, B.Sq>, +g: U32, e: {Some{g} == gk(b, h, t, all) : Maybe<&2, U32>},
    ih: {Some{g} == B.c3.good(t, all) : Maybe<&2, U32>} -> {is.head(t, g) == True{} : Bool}) ->
    {Bool.or(U32.is_eq(h, g), is.head(t, g)) == True{} : Bool}:
  match b:
    case True{}:
      or_r_true(U32.is_eq(h, g), is.head(t, g), ih(e))
    case False{}:
      %some_inj(g, h, e) : {Bool.or(U32.is_eq(_, g), is.head(t, g)) == True{} : Bool}
      %Equal.sym(Bool, U32.is_eq(g, g), True{}, u32_is_eq_refl(g)) : {Bool.or(_, is.head(t, g)) == True{} : Bool}
      {==}

def good_head(cs: List<&2, B.Sq>, +all: List<&2, B.Sq>, +g: U32, e: {Some{g} == B.c3.good(cs, all) : Maybe<&2, U32>}) -> {is.head(cs, g) == True{} : Bool}:
  match cs:
    case Nil{}:
      Empty.absurd({False{} == True{} : Bool}, some_none(g, e))
    case Con{c, +t}:
      match c:
        case B.Sq{+o, xs}:
          match xs:
            case Nil{}:
              good_head(t, all, g, e)
            case Con{+h, +r}:
              good_head.k(B.in_tails(all, h), h, t, all, g, e, f => good_head(t, all, g, f))

def good_free.k(b: Bool, +h: U32, +t: List<&2, B.Sq>, +all: List<&2, B.Sq>, +g: U32, eq: {b == B.in_tails(all, h) : Bool},
    e: {Some{g} == gk(b, h, t, all) : Maybe<&2, U32>},
    ih: {Some{g} == B.c3.good(t, all) : Maybe<&2, U32>} -> {B.in_tails(all, g) == False{} : Bool}) ->
    {B.in_tails(all, g) == False{} : Bool}:
  match b:
    case True{}:
      ih(e)
    case False{}:
      %Equal.sym(U32, g, h, some_inj(g, h, e)) : {B.in_tails(all, _) == False{} : Bool}
      Equal.sym(Bool, False{}, B.in_tails(all, h), eq)

def good_free(cs: List<&2, B.Sq>, +all: List<&2, B.Sq>, +g: U32, e: {Some{g} == B.c3.good(cs, all) : Maybe<&2, U32>}) -> {B.in_tails(all, g) == False{} : Bool}:
  match cs:
    case Nil{}:
      Empty.absurd({B.in_tails(all, g) == False{} : Bool}, some_none(g, e))
    case Con{c, +t}:
      match c:
        case B.Sq{+o, xs}:
          match xs:
            case Nil{}:
              good_free(t, all, g, e)
            case Con{+h, +r}:
              good_free.k(B.in_tails(all, h), h, t, all, g, {==}, e, f => good_free(t, all, g, f))

# a free head taken before an order sound for the lists after: sound
def sound_cons(+g: U32, m: B.Mg, +ss: List<&2, B.Sq>, +hf: {B.in_tails(ss, g) == False{} : Bool}, +hh: {is.head(ss, g) == True{} : Bool},
    +ih: {minv(m, B.c3.take(ss, g)) == True{} : Bool}) -> {minv(mcons(g, m), ss) == True{} : Bool}:
  match m:
    case B.MOk{+o}:
      and_intro(B.sqs.kept(ss, Con{g, o}), Bool.and(B.distinct(Con{g, o}), sqs.all(Con{g, o}, ss)),
        kept_cons(ss, g, o, and_l(B.sqs.kept(B.c3.take(ss, g), o), Bool.and(B.distinct(o), sqs.all(o, B.c3.take(ss, g))), ih)),
        and_intro(B.distinct(Con{g, o}), sqs.all(Con{g, o}, ss),
          and_intro(Bool.not(B.has(o, g)), B.distinct(o),
            not_false(B.has(o, g), all_not(o, B.c3.take(ss, g), g,
              and_r(B.distinct(o), sqs.all(o, B.c3.take(ss, g)), and_r(B.sqs.kept(B.c3.take(ss, g), o), Bool.and(B.distinct(o), sqs.all(o, B.c3.take(ss, g))), ih)),
              take_gone(ss, g, hf))),
            and_l(B.distinct(o), sqs.all(o, B.c3.take(ss, g)), and_r(B.sqs.kept(B.c3.take(ss, g), o), Bool.and(B.distinct(o), sqs.all(o, B.c3.take(ss, g))), ih))),
          and_intro(sqs.has(ss, g), sqs.all(o, ss), head_has(ss, g, hh),
            all_take(o, ss, g, and_r(B.distinct(o), sqs.all(o, B.c3.take(ss, g)), and_r(B.sqs.kept(B.c3.take(ss, g), o), Bool.and(B.distinct(o), sqs.all(o, B.c3.take(ss, g))), ih))))))
    case B.MFail{x}:
      {==}

def sound_k(mb: Maybe<&2, U32>, +k: Nat, +s: B.Sq, +t: List<&2, B.Sq>, +e: {mb == B.c3.good(Con{s, t}, Con{s, t}) : Maybe<&2, U32>},
    ih: @g:U32 -> {minv(mrest(k, B.c3.take(Con{s, t}, g)), B.c3.take(Con{s, t}, g)) == True{} : Bool}) ->
    {minv(mrest_k(mb, k, s, t), Con{s, t}) == True{} : Bool}:
  match mb:
    case None{}:
      {==}
    case Some{+g}:
      sound_cons(g, mrest(k, B.c3.take(Con{s, t}, g)), Con{s, t}, good_free(Con{s, t}, Con{s, t}, g, e), good_head(Con{s, t}, Con{s, t}, g, e), ih(g))

def mrest_sound(n: Nat, +seqs: List<&2, B.Sq>) -> {minv(mrest(n, seqs), seqs) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+(+k):
      match seqs:
        case Nil{}:
          {==}
        case Con{+s, +t}:
          sound_k(B.c3.good(Con{s, t}, Con{s, t}), k, s, t, {==}, +g => mrest_sound(k, B.c3.take(Con{s, t}, g)))

def sound_of(m: B.Mg, +ss: List<&2, B.Sq>, +h: {minv(m, ss) == True{} : Bool}) -> {B.mg.sound(m, ss) == True{} : Bool}:
  match m:
    case B.MOk{+o}:
      and_intro(B.sqs.kept(ss, o), B.distinct(o), and_l(B.sqs.kept(ss, o), Bool.and(B.distinct(o), sqs.all(o, ss)), h),
        and_l(B.distinct(o), sqs.all(o, ss), and_r(B.sqs.kept(ss, o), Bool.and(B.distinct(o), sqs.all(o, ss)), h)))
    case B.MFail{x}:
      {==}

def Laws.c3.sound(n, seqs):
  %merge_acc(n, seqs, Nil{}) : {B.mg.sound(_, seqs) == True{} : Bool}
  %mpre_nil(mrest(n, seqs)) : {B.mg.sound(_, seqs) == True{} : Bool}
  sound_of(mrest(n, seqs), seqs, mrest_sound(n, seqs))

# no list empty
def sqs.full(ss: List<&2, B.Sq>) -> Bool:
  match ss:
    case Nil{}:
      True{}
    case Con{s, t}:
      match s:
        case B.Sq{+o, xs}:
          match xs:
            case Nil{}:
              False{}
            case Con{x, r}:
              sqs.full(t)

def eq_is(+x0: U32, +y: U32, +x: U32, e: {x0 == y : U32}, h: {U32.is_eq(x0, x) == True{} : Bool}) -> {U32.is_eq(y, x) == True{} : Bool}:
  %e : {U32.is_eq(_, x) == True{} : Bool}
  h

def sub_has.k(b: Bool, +y: U32, +yr: List<&2, U32>, +x0: U32, +r: List<&2, U32>, +x: U32, eq: {b == U32.is_eq(x0, y) : Bool},
    hs: {sub_k(b, yr, x0, r) == True{} : Bool}, hx: {B.has(Con{x0, r}, x) == True{} : Bool},
    ih1: @p:{B.subseq(yr, r) == True{} : Bool} -> @q:{B.has(r, x) == True{} : Bool} -> {B.has(yr, x) == True{} : Bool},
    ih2: @p:{B.subseq(yr, Con{x0, r}) == True{} : Bool} -> {B.has(yr, x) == True{} : Bool}) ->
    {B.has(Con{y, yr}, x) == True{} : Bool}:
  match b:
    case True{}:
      or_map(U32.is_eq(x0, x), B.has(r, x), U32.is_eq(y, x), B.has(yr, x), hx,
        p => eq_is(x0, y, x, u32_eq_of_is_eq(x0, y, Equal.sym(Bool, True{}, U32.is_eq(x0, y), eq)), p), q => ih1(hs, q))
    case False{}:
      or_r_true(U32.is_eq(y, x), B.has(yr, x), ih2(hs))

# an object of a subsequence is an object of the order
def sub_has(ys: List<&2, U32>, xs: List<&2, U32>, +x: U32, hs: {B.subseq(ys, xs) == True{} : Bool}, +hx: {B.has(xs, x) == True{} : Bool}) ->
    {B.has(ys, x) == True{} : Bool}:
  match ys:
    case Nil{}:
      match xs:
        case Nil{}:
          Empty.absurd({B.has(Nil{}, x) == True{} : Bool}, MB.false_ne_true()(hx))
        case Con{x0, r}:
          Empty.absurd({B.has(Nil{}, x) == True{} : Bool}, MB.false_ne_true()(hs))
    case Con{+y, +yr}:
      match xs:
        case Nil{}:
          Empty.absurd({B.has(Con{y, yr}, x) == True{} : Bool}, MB.false_ne_true()(hx))
        case Con{+x0, +r}:
          sub_has.k(U32.is_eq(x0, y), y, yr, x0, r, x, {==}, hs, hx, p => q => sub_has(yr, r, x, p, q), p => sub_has(yr, Con{x0, r}, x, p, hx))

def yr_has(b: Bool, +a: U32, +r: List<&2, U32>, +y: U32, +yr: List<&2, U32>, hs: {sub_k(b, yr, a, r) == True{} : Bool}, hr: {B.has(r, y) == True{} : Bool}) ->
    {B.has(yr, y) == True{} : Bool}:
  match b:
    case True{}:
      sub_has(yr, r, y, hs, hr)
    case False{}:
      sub_has(yr, Con{a, r}, y, hs, or_r_true(U32.is_eq(a, y), B.has(r, y), hr))

def tail_free.k(c: Bool, +a: U32, +r: List<&2, U32>, +y: U32, +yr: List<&2, U32>, eqc: {c == B.has(r, y) : Bool},
    hs: {B.subseq(Con{y, yr}, Con{a, r}) == True{} : Bool}, hd: {B.has(yr, y) == False{} : Bool}) -> {B.has(r, y) == False{} : Bool}:
  match c:
    case True{}:
      Empty.absurd({B.has(r, y) == False{} : Bool}, both(B.has(yr, y), yr_has(U32.is_eq(a, y), a, r, y, yr, hs, Equal.sym(Bool, True{}, B.has(r, y), eqc)), hd))
    case False{}:
      Equal.sym(Bool, False{}, B.has(r, y), eqc)

# an object first in an order holding it once is in no tail of a list
# the order keeps
def tails_none(ss: List<&2, B.Sq>, +y: U32, +yr: List<&2, U32>, +hk: {B.sqs.kept(ss, Con{y, yr}) == True{} : Bool}, +hd: {B.has(yr, y) == False{} : Bool}) ->
    {B.in_tails(ss, y) == False{} : Bool}:
  match ss:
    case Nil{}:
      {==}
    case Con{s, +t}:
      match s:
        case B.Sq{+o, xs}:
          match xs:
            case Nil{}:
              tails_none(t, y, yr, and_r(B.subseq(Con{y, yr}, Nil{}), B.sqs.kept(t, Con{y, yr}), hk), hd)
            case Con{+a, +r}:
              %Equal.sym(Bool, B.has(r, y), False{}, tail_free.k(B.has(r, y), a, r, y, yr, {==},
                and_l(B.subseq(Con{y, yr}, Con{a, r}), B.sqs.kept(t, Con{y, yr}), hk), hd)) : {Bool.or(_, B.in_tails(t, y)) == False{} : Bool}
              tails_none(t, y, yr, and_r(B.subseq(Con{y, yr}, Con{a, r}), B.sqs.kept(t, Con{y, yr}), hk), hd)

def tails_eq(+all: List<&2, B.Sq>, +h: U32, +y: U32, e: {h == y : U32}, ht: {B.in_tails(all, y) == False{} : Bool}) -> {B.in_tails(all, h) == False{} : Bool}:
  %Equal.sym(U32, h, y, e) : {B.in_tails(all, _) == False{} : Bool}
  ht

def good_some.k(b: Bool, +h: U32, +t: List<&2, B.Sq>, +all: List<&2, B.Sq>, +y: U32, eq: {b == B.in_tails(all, h) : Bool},
    hh: {Bool.or(U32.is_eq(h, y), is.head(t, y)) == True{} : Bool}, ht: {B.in_tails(all, y) == False{} : Bool},
    ih: {is.head(t, y) == True{} : Bool} -> {Maybe.is_some(&2, U32, B.c3.good(t, all)) == True{} : Bool}) ->
    {Maybe.is_some(&2, U32, gk(b, h, t, all)) == True{} : Bool}:
  match b:
    case True{}:
      or_cases(U32.is_eq(h, y), is.head(t, y), Maybe.is_some(&2, U32, B.c3.good(t, all)), hh,
        p => Empty.absurd({Maybe.is_some(&2, U32, B.c3.good(t, all)) == True{} : Bool},
          both(B.in_tails(all, h), Equal.sym(Bool, True{}, B.in_tails(all, h), eq), tails_eq(all, h, y, u32_eq_of_is_eq(h, y, p), ht))),
        ih)
    case False{}:
      {==}

# a head in no tail: the merge's search finds a head
def good_some(cs: List<&2, B.Sq>, +all: List<&2, B.Sq>, +y: U32, hh: {is.head(cs, y) == True{} : Bool}, +ht: {B.in_tails(all, y) == False{} : Bool}) ->
    {Maybe.is_some(&2, U32, B.c3.good(cs, all)) == True{} : Bool}:
  match cs:
    case Nil{}:
      hh
    case Con{c, +t}:
      match c:
        case B.Sq{+o, xs}:
          match xs:
            case Nil{}:
              good_some(t, all, y, hh, ht)
            case Con{+h, +r}:
              good_some.k(B.in_tails(all, h), h, t, all, y, {==}, hh, ht, p => good_some(t, all, y, p, ht))

def skip1(+x: U32, +r: List<&2, U32>, +y: U32, +yr: List<&2, U32>, e: {U32.is_eq(x, y) == False{} : Bool},
    h: {B.subseq(Con{y, yr}, Con{x, r}) == True{} : Bool}) -> {B.subseq(yr, Con{x, r}) == True{} : Bool}:
  %e : {sub_k(_, yr, x, r) == True{} : Bool}
  h

# lists none of which an object heads, kept by an order after it: kept
# by that order
def kept_skip(ss: List<&2, B.Sq>, +y: U32, +yr: List<&2, U32>, +hk: {B.sqs.kept(ss, Con{y, yr}) == True{} : Bool}, +hh: {is.head(ss, y) == False{} : Bool}) ->
    {B.sqs.kept(ss, yr) == True{} : Bool}:
  match ss:
    case Nil{}:
      {==}
    case Con{s, +t}:
      match s:
        case B.Sq{+o, xs}:
          match xs:
            case Nil{}:
              and_intro(B.subseq(yr, Nil{}), B.sqs.kept(t, yr), sub_nil(yr),
                kept_skip(t, y, yr, and_r(B.subseq(Con{y, yr}, Nil{}), B.sqs.kept(t, Con{y, yr}), hk), hh))
            case Con{+x, +r}:
              and_intro(B.subseq(yr, Con{x, r}), B.sqs.kept(t, yr),
                skip1(x, r, y, yr, or_false_l(U32.is_eq(x, y), is.head(t, y), hh), and_l(B.subseq(Con{y, yr}, Con{x, r}), B.sqs.kept(t, Con{y, yr}), hk)),
                kept_skip(t, y, yr, and_r(B.subseq(Con{y, yr}, Con{x, r}), B.sqs.kept(t, Con{y, yr}), hk), or_false_r(U32.is_eq(x, y), is.head(t, y), hh)))

def good_of.k(c: Bool, +y: U32, +yr: List<&2, U32>, +s: B.Sq, +t: List<&2, B.Sq>, eq: {c == is.head(Con{s, t}, y) : Bool},
    +hk: {B.sqs.kept(Con{s, t}, Con{y, yr}) == True{} : Bool}, ht: {B.in_tails(Con{s, t}, y) == False{} : Bool},
    ih: {B.sqs.kept(Con{s, t}, yr) == True{} : Bool} -> {Maybe.is_some(&2, U32, B.c3.good(Con{s, t}, Con{s, t})) == True{} : Bool}) ->
    {Maybe.is_some(&2, U32, B.c3.good(Con{s, t}, Con{s, t})) == True{} : Bool}:
  match c:
    case True{}:
      good_some(Con{s, t}, Con{s, t}, y, Equal.sym(Bool, True{}, is.head(Con{s, t}, y), eq), ht)
    case False{}:
      ih(kept_skip(Con{s, t}, y, yr, hk, Equal.sym(Bool, False{}, is.head(Con{s, t}, y), eq)))

# lists, none empty, kept by an order holding each object once: a head
# is free, the order's first object a list holds
def good_of(ys: List<&2, U32>, +s: B.Sq, +t: List<&2, B.Sq>, +hk: {B.sqs.kept(Con{s, t}, ys) == True{} : Bool},
    +hd: {B.distinct(ys) == True{} : Bool}, +hf: {sqs.full(Con{s, t}) == True{} : Bool}) ->
    {Maybe.is_some(&2, U32, B.c3.good(Con{s, t}, Con{s, t})) == True{} : Bool}:
  match ys:
    case Nil{}:
      match s:
        case B.Sq{+o, xs}:
          match xs:
            case Nil{}:
              Empty.absurd({Maybe.is_some(&2, U32, B.c3.good(Con{B.Sq{o, Nil{}}, t}, Con{B.Sq{o, Nil{}}, t})) == True{} : Bool}, MB.false_ne_true()(hf))
            case Con{+x, +r}:
              Empty.absurd({Maybe.is_some(&2, U32, B.c3.good(Con{B.Sq{o, Con{x, r}}, t}, Con{B.Sq{o, Con{x, r}}, t})) == True{} : Bool}, MB.false_ne_true()(hk))
    case Con{+y, +yr}:
      good_of.k(is.head(Con{s, t}, y), y, yr, s, t, {==}, hk,
        tails_none(Con{s, t}, y, yr, hk, not_true(B.has(yr, y), and_l(Bool.not(B.has(yr, y)), B.distinct(yr), hd))),
        p => good_of(yr, s, t, p, and_r(Bool.not(B.has(yr, y)), B.distinct(yr), hd), hf))

def sub_weak.k(b: Bool, +y: U32, +yr: List<&2, U32>, +x: U32, +r: List<&2, U32>, h: {B.subseq(yr, Con{x, r}) == True{} : Bool},
    ht: {B.subseq(yr, r) == True{} : Bool}) -> {sub_k(b, yr, x, r) == True{} : Bool}:
  match b:
    case True{}:
      ht
    case False{}:
      h

# an object before an order keeping a list: the list kept still, given
# that the order keeps a list's rest where it keeps the list
def sub_weak(+y: U32, +yr: List<&2, U32>, xs: List<&2, U32>, +h: {B.subseq(yr, xs) == True{} : Bool},
    tl: @x:U32 -> @r:List<&2, U32> -> @p:{B.subseq(yr, Con{x, r}) == True{} : Bool} -> {B.subseq(yr, r) == True{} : Bool}) ->
    {B.subseq(Con{y, yr}, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      sub_weak.k(U32.is_eq(x, y), y, yr, x, r, h, tl(x, r, h))

def sub_tail.k(b: Bool, +y: U32, +yr: List<&2, U32>, +x: U32, +r: List<&2, U32>, h: {sub_k(b, yr, x, r) == True{} : Bool},
    ih: @p:{B.subseq(yr, Con{x, r}) == True{} : Bool} -> {B.subseq(yr, r) == True{} : Bool},
    wk: @p:{B.subseq(yr, r) == True{} : Bool} -> {B.subseq(Con{y, yr}, r) == True{} : Bool}) ->
    {B.subseq(Con{y, yr}, r) == True{} : Bool}:
  match b:
    case True{}:
      wk(h)
    case False{}:
      wk(ih(h))

# where an order keeps a list, it keeps the list's rest
def sub_tail(ys: List<&2, U32>, +x: U32, +r: List<&2, U32>, h: {B.subseq(ys, Con{x, r}) == True{} : Bool}) -> {B.subseq(ys, r) == True{} : Bool}:
  match ys:
    case Nil{}:
      Empty.absurd({B.subseq(Nil{}, r) == True{} : Bool}, MB.false_ne_true()(h))
    case Con{+y, +yr}:
      sub_tail.k(U32.is_eq(x, y), y, yr, x, r, h, p => sub_tail(yr, x, r, p),
        p => sub_weak(y, yr, r, p, x2 => r2 => q => sub_tail(yr, x2, r2, q)))

def drop_kept.k(b: Bool, +ys: List<&2, U32>, +x: U32, +r: List<&2, U32>, h: {B.subseq(ys, Con{x, r}) == True{} : Bool}) ->
    {B.subseq(ys, dk(b, x, r)) == True{} : Bool}:
  match b:
    case True{}:
      sub_tail(ys, x, r, h)
    case False{}:
      h

def keep_kept_in(+o: U32, d: List<&2, U32>, +t: List<&2, B.Sq>, +ys: List<&2, U32>, hd: {B.subseq(ys, d) == True{} : Bool},
    ht: {B.sqs.kept(t, ys) == True{} : Bool}) -> {B.sqs.kept(B.c3.keep(o, d, t), ys) == True{} : Bool}:
  match d:
    case Nil{}:
      ht
    case Con{+x, +r}:
      and_intro(B.subseq(ys, Con{x, r}), B.sqs.kept(t, ys), hd, ht)

# lists an order keeps, a head taken from them: kept
def kept_take(ss: List<&2, B.Sq>, +g: U32, +ys: List<&2, U32>, +hk: {B.sqs.kept(ss, ys) == True{} : Bool}) -> {B.sqs.kept(B.c3.take(ss, g), ys) == True{} : Bool}:
  match ss:
    case Nil{}:
      {==}
    case Con{s, +t}:
      match s:
        case B.Sq{+o, xs}:
          match xs:
            case Nil{}:
              kept_take(t, g, ys, and_r(B.subseq(ys, Nil{}), B.sqs.kept(t, ys), hk))
            case Con{+x, +r}:
              keep_kept_in(o, dk(U32.is_eq(x, g), x, r), B.c3.take(t, g), ys,
                drop_kept.k(U32.is_eq(x, g), ys, x, r, and_l(B.subseq(ys, Con{x, r}), B.sqs.kept(t, ys), hk)),
                kept_take(t, g, ys, and_r(B.subseq(ys, Con{x, r}), B.sqs.kept(t, ys), hk)))

def keep_full(+o: U32, d: List<&2, U32>, +t: List<&2, B.Sq>, h: {sqs.full(t) == True{} : Bool}) -> {sqs.full(B.c3.keep(o, d, t)) == True{} : Bool}:
  match d:
    case Nil{}:
      h
    case Con{x, r}:
      h

# a take drops the lists it empties
def full_take(ss: List<&2, B.Sq>, +g: U32) -> {sqs.full(B.c3.take(ss, g)) == True{} : Bool}:
  match ss:
    case Nil{}:
      {==}
    case Con{s, +t}:
      match s:
        case B.Sq{+o, +xs}:
          keep_full(o, B.c3.head.drop(xs, g), B.c3.take(t, g), full_take(t, g))

# The fuel: a take shortens the lists, by one at least where it takes a
# head

def le_add_l(a: Nat, +b: Nat) -> MNat.le(b, Nat.add(a, b)):
  match a:
    case 0n:
      MNat.le_refl(b)
    case 1n+(+p):
      MNat.le_trans(b, Nat.add(p, b), 1n+Nat.add(p, b), le_add_l(p, b), MNat.le_succ(Nat.add(p, b)))

def le_add2(a2: Nat, +a: Nat, +b2: Nat, +b: Nat, h1: MNat.le(a2, a), h2: MNat.le(b2, b)) -> MNat.le(Nat.add(a2, b2), Nat.add(a, b)):
  match a2 a:
    case 0n _:
      MNat.le_trans(b2, b, Nat.add(a, b), h2, le_add_l(a, b))
    case 1n+p 0n:
      Empty.absurd(MNat.le(Nat.add(1n+p, b2), Nat.add(0n, b)), MB.false_ne_true()(h1))
    case 1n+p 1n+q:
      le_add2(p, q, b2, b, h1, h2)

def drop_len.k(b: Bool, +x: U32, +r: List<&2, U32>) -> MNat.le(List.length(&2, U32, dk(b, x, r)), List.length(&2, U32, Con{x, r})):
  match b:
    case True{}:
      MNat.le_succ(List.length(&2, U32, r))
    case False{}:
      MNat.le_refl(List.length(&2, U32, Con{x, r}))

def drop_len(xs: List<&2, U32>, +g: U32) -> MNat.le(List.length(&2, U32, B.c3.head.drop(xs, g)), List.length(&2, U32, xs)):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      drop_len.k(U32.is_eq(x, g), x, r)

def keep_len(+o: U32, d: List<&2, U32>, +t: List<&2, B.Sq>) -> {Nat.add(List.length(&2, U32, d), B.sqs.len(t)) == B.sqs.len(B.c3.keep(o, d, t)) : Nat}:
  match d:
    case Nil{}:
      {==}
    case Con{x, r}:
      {==}

def len_take(ss: List<&2, B.Sq>, +g: U32) -> MNat.le(B.sqs.len(B.c3.take(ss, g)), B.sqs.len(ss)):
  match ss:
    case Nil{}:
      {==}
    case Con{s, +t}:
      match s:
        case B.Sq{+o, +xs}:
          %keep_len(o, B.c3.head.drop(xs, g), B.c3.take(t, g)) : MNat.le(_, B.sqs.len(Con{B.Sq{o, xs}, t}))
          le_add2(List.length(&2, U32, B.c3.head.drop(xs, g)), List.length(&2, U32, xs), B.sqs.len(B.c3.take(t, g)), B.sqs.len(t),
            drop_len(xs, g), len_take(t, g))

def or_drop(+a: Bool, +b: Bool, ea: {a == False{} : Bool}, h: {Bool.or(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      Empty.absurd({b == True{} : Bool}, MB.true_ne_false()(ea))
    case False{}:
      h

def lt_k(b: Bool, +x: U32, +r: List<&2, U32>, +t: List<&2, B.Sq>, +g: U32, eq: {b == U32.is_eq(x, g) : Bool},
    hh: {Bool.or(U32.is_eq(x, g), is.head(t, g)) == True{} : Bool},
    ih: {is.head(t, g) == True{} : Bool} -> MNat.le(1n+B.sqs.len(B.c3.take(t, g)), B.sqs.len(t))) ->
    MNat.le(1n+Nat.add(List.length(&2, U32, dk(b, x, r)), B.sqs.len(B.c3.take(t, g))), Nat.add(List.length(&2, U32, Con{x, r}), B.sqs.len(t))):
  match b:
    case True{}:
      le_add2(List.length(&2, U32, r), List.length(&2, U32, r), B.sqs.len(B.c3.take(t, g)), B.sqs.len(t),
        MNat.le_refl(List.length(&2, U32, r)), len_take(t, g))
    case False{}:
      %MNat.add_succ(List.length(&2, U32, r), B.sqs.len(B.c3.take(t, g))) : MNat.le(_, Nat.add(List.length(&2, U32, r), B.sqs.len(t)))
      le_add2(List.length(&2, U32, r), List.length(&2, U32, r), 1n+B.sqs.len(B.c3.take(t, g)), B.sqs.len(t),
        MNat.le_refl(List.length(&2, U32, r)), ih(or_drop(U32.is_eq(x, g), is.head(t, g), Equal.sym(Bool, False{}, U32.is_eq(x, g), eq), hh)))

# a take of a head shortens the lists
def len_take_lt(ss: List<&2, B.Sq>, +g: U32, hh: {is.head(ss, g) == True{} : Bool}) -> MNat.le(1n+B.sqs.len(B.c3.take(ss, g)), B.sqs.len(ss)):
  match ss:
    case Nil{}:
      Empty.absurd(MNat.le(1n+B.sqs.len(B.c3.take(Nil{}, g)), B.sqs.len(Nil{})), MB.false_ne_true()(hh))
    case Con{s, +t}:
      match s:
        case B.Sq{+o, xs}:
          match xs:
            case Nil{}:
              len_take_lt(t, g, hh)
            case Con{+x, +r}:
              %keep_len(o, dk(U32.is_eq(x, g), x, r), B.c3.take(t, g)) : MNat.le(1n+_, B.sqs.len(Con{B.Sq{o, Con{x, r}}, t}))
              lt_k(U32.is_eq(x, g), x, r, t, g, {==}, hh, p => len_take_lt(t, g, p))

def some_of(mb: Maybe<&2, U32>, +x: Maybe<&2, U32>, eq: {mb == x : Maybe<&2, U32>}, h: {Maybe.is_some(&2, U32, x) == True{} : Bool}) ->
    {Maybe.is_some(&2, U32, mb) == True{} : Bool}:
  %Equal.sym(Maybe<&2, U32>, mb, x, eq) : {Maybe.is_some(&2, U32, _) == True{} : Bool}
  h

def ok_k(mb: Maybe<&2, U32>, +k: Nat, +s: B.Sq, +t: List<&2, B.Sq>, +out: List<&2, U32>, eq: {mb == B.c3.good(Con{s, t}, Con{s, t}) : Maybe<&2, U32>},
    hs: {Maybe.is_some(&2, U32, B.c3.good(Con{s, t}, Con{s, t})) == True{} : Bool},
    ih: @g:U32 -> @e:{Some{g} == B.c3.good(Con{s, t}, Con{s, t}) : Maybe<&2, U32>} -> {B.mg.ok(B.c3.merge(k, B.c3.take(Con{s, t}, g), Con{g, out})) == True{} : Bool}) ->
    {B.mg.ok(merge_k(mb, k, s, t, out)) == True{} : Bool}:
  match mb:
    case None{}:
      Empty.absurd({False{} == True{} : Bool}, MB.false_ne_true()(some_of(None{}, B.c3.good(Con{s, t}, Con{s, t}), eq, hs)))
    case Some{+g}:
      ih(g, eq)

# lists, none empty, kept by an order holding each object once, with
# fuel past their lengths: the merge succeeds
def merge_ok(n: Nat, +ss: List<&2, B.Sq>, +ys: List<&2, U32>, +out: List<&2, U32>, +hf: MNat.le(1n+B.sqs.len(ss), n),
    +hk: {B.sqs.kept(ss, ys) == True{} : Bool}, +hd: {B.distinct(ys) == True{} : Bool}, +hu: {sqs.full(ss) == True{} : Bool}) ->
    {B.mg.ok(B.c3.merge(n, ss, out)) == True{} : Bool}:
  match n:
    case 0n:
      Empty.absurd({B.mg.ok(B.c3.merge(0n, ss, out)) == True{} : Bool}, MB.false_ne_true()(hf))
    case 1n+(+k):
      match ss:
        case Nil{}:
          {==}
        case Con{+s, +t}:
          ok_k(B.c3.good(Con{s, t}, Con{s, t}), k, s, t, out, {==}, good_of(ys, s, t, hk, hd, hu),
            +g => +e => merge_ok(k, B.c3.take(Con{s, t}, g), ys, Con{g, out},
              MNat.le_trans(1n+B.sqs.len(B.c3.take(Con{s, t}, g)), B.sqs.len(Con{s, t}), k, len_take_lt(Con{s, t}, g, good_head(Con{s, t}, Con{s, t}, g, e)), hf),
              kept_take(Con{s, t}, g, ys, hk), hd, full_take(Con{s, t}, g)))

def ok_mg(+id: U32, m: B.Mg) -> {B.mg.ok(m) == B.lz.ok(B.lin.mg(id, m)) : Bool}:
  match m:
    case B.MOk{ord}:
      {==}
    case B.MFail{ss}:
      {==}

def Laws.c3.complete(id, ps, seqs, ys, h1, h2):
  %ok_mg(id, B.c3.merge(1n+B.sqs.len(List.append(&2, B.Sq, seqs, [B.Sq{id, ps}])), B.c3.take(List.append(&2, B.Sq, seqs, [B.Sq{id, ps}]), 4294967295), Nil{})) :
    {_ == True{} : Bool}
  merge_ok(1n+B.sqs.len(List.append(&2, B.Sq, seqs, [B.Sq{id, ps}])), B.c3.take(List.append(&2, B.Sq, seqs, [B.Sq{id, ps}]), 4294967295), ys, Nil{},
    len_take(List.append(&2, B.Sq, seqs, [B.Sq{id, ps}]), 4294967295), kept_take(List.append(&2, B.Sq, seqs, [B.Sq{id, ps}]), 4294967295, ys, h1), h2,
    full_take(List.append(&2, B.Sq, seqs, [B.Sq{id, ps}]), 4294967295))

# U32 sums
# --------
#
# U32 addition wraps at 2^32: a sum's to_nat is the naturals' sum mod
# 2^32 (the hub's `u32_add_wrap`). Reasoned under a modulus N, the wrap
# law passed in, so that the power is never unfolded: addition is then
# associative and commutative, as the sharing law's two sums need.

# a multiple of N added before a natural: its remainder the same
def mod_mul(q: Nat, +n: Nat, +a: Nat) -> {Nat.mod(a, n) == Nat.mod(Nat.add(Nat.mul(q, n), a), n) : Nat}:
  match q:
    case 0n:
      {==}
    case 1n+(+p):
      %Equal.sym(Nat, Nat.add(Nat.add(n, Nat.mul(p, n)), a), Nat.add(n, Nat.add(Nat.mul(p, n), a)), MNat.add_assoc(n, Nat.mul(p, n), a)) :
        {Nat.mod(a, n) == Nat.mod(_, n) : Nat}
      %Equal.sym(Nat, Nat.mod(Nat.add(n, Nat.add(Nat.mul(p, n), a)), n), Nat.mod(Nat.add(Nat.mul(p, n), a), n), MNat.add_mod_left(Nat.add(Nat.mul(p, n), a), n)) :
        {Nat.mod(a, n) == _ : Nat}
      mod_mul(p, n, a)

# a remainder added first: the sum's remainder
def mod_add_l(+x: Nat, +y: Nat, +n: Nat) -> {Nat.mod(Nat.add(Nat.mod(x, n), y), n) == Nat.mod(Nat.add(x, y), n) : Nat}:
  %MNat.mod_add_div(x, n) : {Nat.mod(Nat.add(Nat.mod(x, n), y), n) == Nat.mod(Nat.add(_, y), n) : Nat}
  %MNat.add_comm(Nat.mul(n, Nat.div(x, n)), Nat.mod(x, n)) : {Nat.mod(Nat.add(Nat.mod(x, n), y), n) == Nat.mod(Nat.add(_, y), n) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(Nat.mul(n, Nat.div(x, n)), Nat.mod(x, n)), y), Nat.add(Nat.mul(n, Nat.div(x, n)), Nat.add(Nat.mod(x, n), y)),
      MNat.add_assoc(Nat.mul(n, Nat.div(x, n)), Nat.mod(x, n), y)) :
    {Nat.mod(Nat.add(Nat.mod(x, n), y), n) == Nat.mod(_, n) : Nat}
  %MNat.mul_comm(Nat.div(x, n), n) : {Nat.mod(Nat.add(Nat.mod(x, n), y), n) == Nat.mod(Nat.add(_, Nat.add(Nat.mod(x, n), y)), n) : Nat}
  mod_mul(Nat.div(x, n), n, Nat.add(Nat.mod(x, n), y))

# the sums' wraps, each an equation, as a proof function is used once
def u32_assoc_n(+n: Nat, +a: U32, +b: U32, +c: U32, w1: {U32.to_nat(U32.add(U32.add(a, b), c)) == Nat.mod(Nat.add(U32.to_nat(U32.add(a, b)), U32.to_nat(c)), n) : Nat}, w2: {U32.to_nat(U32.add(a, b)) == Nat.mod(Nat.add(U32.to_nat(a), U32.to_nat(b)), n) : Nat},
    w3: {U32.to_nat(U32.add(a, U32.add(b, c))) == Nat.mod(Nat.add(U32.to_nat(a), U32.to_nat(U32.add(b, c))), n) : Nat}, w4: {U32.to_nat(U32.add(b, c)) == Nat.mod(Nat.add(U32.to_nat(b), U32.to_nat(c)), n) : Nat}) -> {U32.to_nat(U32.add(U32.add(a, b), c)) == U32.to_nat(U32.add(a, U32.add(b, c))) : Nat}:
  %Equal.sym(Nat, U32.to_nat(U32.add(U32.add(a, b), c)), Nat.mod(Nat.add(U32.to_nat(U32.add(a, b)), U32.to_nat(c)), n), w1) : {_ == U32.to_nat(U32.add(a, U32.add(b, c))) : Nat}
  %Equal.sym(Nat, U32.to_nat(U32.add(a, b)), Nat.mod(Nat.add(U32.to_nat(a), U32.to_nat(b)), n), w2) : {Nat.mod(Nat.add(_, U32.to_nat(c)), n) == U32.to_nat(U32.add(a, U32.add(b, c))) : Nat}
  %Equal.sym(Nat, Nat.mod(Nat.add(Nat.mod(Nat.add(U32.to_nat(a), U32.to_nat(b)), n), U32.to_nat(c)), n), Nat.mod(Nat.add(Nat.add(U32.to_nat(a), U32.to_nat(b)), U32.to_nat(c)), n), mod_add_l(Nat.add(U32.to_nat(a), U32.to_nat(b)), U32.to_nat(c), n)) : {_ == U32.to_nat(U32.add(a, U32.add(b, c))) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(U32.to_nat(a), U32.to_nat(b)), U32.to_nat(c)), Nat.add(U32.to_nat(a), Nat.add(U32.to_nat(b), U32.to_nat(c))), MNat.add_assoc(U32.to_nat(a), U32.to_nat(b), U32.to_nat(c))) : {Nat.mod(_, n) == U32.to_nat(U32.add(a, U32.add(b, c))) : Nat}
  %Equal.sym(Nat, U32.to_nat(U32.add(a, U32.add(b, c))), Nat.mod(Nat.add(U32.to_nat(a), U32.to_nat(U32.add(b, c))), n), w3) : {Nat.mod(Nat.add(U32.to_nat(a), Nat.add(U32.to_nat(b), U32.to_nat(c))), n) == _ : Nat}
  %Equal.sym(Nat, U32.to_nat(U32.add(b, c)), Nat.mod(Nat.add(U32.to_nat(b), U32.to_nat(c)), n), w4) : {Nat.mod(Nat.add(U32.to_nat(a), Nat.add(U32.to_nat(b), U32.to_nat(c))), n) == Nat.mod(Nat.add(U32.to_nat(a), _), n) : Nat}
  %MNat.add_comm(Nat.mod(Nat.add(U32.to_nat(b), U32.to_nat(c)), n), U32.to_nat(a)) : {Nat.mod(Nat.add(U32.to_nat(a), Nat.add(U32.to_nat(b), U32.to_nat(c))), n) == Nat.mod(_, n) : Nat}
  %Equal.sym(Nat, Nat.mod(Nat.add(Nat.mod(Nat.add(U32.to_nat(b), U32.to_nat(c)), n), U32.to_nat(a)), n), Nat.mod(Nat.add(Nat.add(U32.to_nat(b), U32.to_nat(c)), U32.to_nat(a)), n), mod_add_l(Nat.add(U32.to_nat(b), U32.to_nat(c)), U32.to_nat(a), n)) : {Nat.mod(Nat.add(U32.to_nat(a), Nat.add(U32.to_nat(b), U32.to_nat(c))), n) == _ : Nat}
  %MNat.add_comm(U32.to_nat(a), Nat.add(U32.to_nat(b), U32.to_nat(c))) : {Nat.mod(Nat.add(U32.to_nat(a), Nat.add(U32.to_nat(b), U32.to_nat(c))), n) == Nat.mod(_, n) : Nat}
  {==}

def u32_comm_n(+n: Nat, +a: U32, +b: U32, w1: {U32.to_nat(U32.add(a, b)) == Nat.mod(Nat.add(U32.to_nat(a), U32.to_nat(b)), n) : Nat}, w2: {U32.to_nat(U32.add(b, a)) == Nat.mod(Nat.add(U32.to_nat(b), U32.to_nat(a)), n) : Nat}) -> {U32.to_nat(U32.add(a, b)) == U32.to_nat(U32.add(b, a)) : Nat}:
  %Equal.sym(Nat, U32.to_nat(U32.add(a, b)), Nat.mod(Nat.add(U32.to_nat(a), U32.to_nat(b)), n), w1) : {_ == U32.to_nat(U32.add(b, a)) : Nat}
  %Equal.sym(Nat, U32.to_nat(U32.add(b, a)), Nat.mod(Nat.add(U32.to_nat(b), U32.to_nat(a)), n), w2) : {Nat.mod(Nat.add(U32.to_nat(a), U32.to_nat(b)), n) == _ : Nat}
  %MNat.add_comm(U32.to_nat(a), U32.to_nat(b)) : {Nat.mod(Nat.add(U32.to_nat(a), U32.to_nat(b)), n) == Nat.mod(_, n) : Nat}
  {==}

# U32 addition is associative and commutative
def u32_assoc(+a: U32, +b: U32, +c: U32) -> {U32.add(U32.add(a, b), c) == U32.add(a, U32.add(b, c)) : U32}:
  MU.u32_to_nat_inj(U32.add(U32.add(a, b), c), U32.add(a, U32.add(b, c)), u32_assoc_n(Nat.pow(2n, 32n), a, b, c,
    MU.u32_add_wrap(U32.add(a, b), c), MU.u32_add_wrap(a, b), MU.u32_add_wrap(a, U32.add(b, c)), MU.u32_add_wrap(b, c)))

def u32_comm(+a: U32, +b: U32) -> {U32.add(a, b) == U32.add(b, a) : U32}:
  MU.u32_to_nat_inj(U32.add(a, b), U32.add(b, a), u32_comm_n(Nat.pow(2n, 32n), a, b, MU.u32_add_wrap(a, b), MU.u32_add_wrap(b, a)))

def u32_one_n(+n: Nat, +a: U32, w: {U32.to_nat(U32.add(a, 0)) == Nat.mod(Nat.add(U32.to_nat(a), U32.to_nat(0)), n) : Nat},
    h: {Nat.mod(U32.to_nat(a), n) == U32.to_nat(a) : Nat}) -> {U32.to_nat(U32.add(a, 0)) == U32.to_nat(a) : Nat}:
  %Equal.sym(Nat, U32.to_nat(U32.add(a, 0)), Nat.mod(Nat.add(U32.to_nat(a), U32.to_nat(0)), n), w) : {_ == U32.to_nat(a) : Nat}
  %Equal.sym(Nat, Nat.add(U32.to_nat(a), 0n), U32.to_nat(a), MNat.add_zero(U32.to_nat(a))) : {Nat.mod(_, n) == U32.to_nat(a) : Nat}
  h

# a zero added: nothing
def u32_zero_r(+a: U32) -> {U32.add(a, 0) == a : U32}:
  MU.u32_to_nat_inj(U32.add(a, 0), a, u32_one_n(Nat.pow(2n, 32n), a, MU.u32_add_wrap(a, 0),
    MNat.mod_eq_of_lt(U32.to_nat(a), Nat.pow(2n, 32n), MU.u32_to_nat_lt(a))))

def u32_zero_l(+a: U32) -> {U32.add(0, a) == a : U32}:
  %Equal.sym(U32, U32.add(0, a), U32.add(a, 0), u32_comm(0, a)) : {_ == a : U32}
  u32_zero_r(a)

# The writer's counters
# ---------------------
#
# A unit's counter of numbered calls, after its body is written: one more
# at each call to it, where the writer is an object's (`wcv`); after all
# of a unit's copies, that once for each (`reps`); which, the sums
# swapped, is what the dispositions weigh each use by (`uses.w`).

# a sum of c, once for each use; c n times
def wsum(rs: List<&2, B.Ru>, +c: U32) -> U32:
  match rs:
    case Nil{}:
      0
    case Con{r, t}:
      U32.add(c, wsum(t, c))

def reps(n: Nat, +c: U32) -> U32:
  match n:
    case 0n:
      0
    case 1n+k:
      U32.add(c, reps(k, c))

def wsum_app(a: List<&2, B.Ru>, +b: List<&2, B.Ru>, +c: U32) -> {U32.add(wsum(a, c), wsum(b, c)) == wsum(List.append(&2, B.Ru, a, b), c) : U32}:
  match a:
    case Nil{}:
      u32_zero_l(wsum(b, c))
    case Con{r, +t}:
      %Equal.sym(U32, U32.add(U32.add(c, wsum(t, c)), wsum(b, c)), U32.add(c, U32.add(wsum(t, c), wsum(b, c))), u32_assoc(c, wsum(t, c), wsum(b, c))) :
        {_ == U32.add(c, wsum(List.append(&2, B.Ru, t, b), c)) : U32}
      %wsum_app(t, b, c) : {U32.add(c, U32.add(wsum(t, c), wsum(b, c))) == U32.add(c, _) : U32}
      {==}

def uses_m_app(a: List<&2, B.Ru>, +b: List<&2, B.Ru>, +ut: B.Ht<B.Un>, +s: B.Ms) ->
    {U32.add(B.uses.m(a, ut, s), B.uses.m(b, ut, s)) == B.uses.m(List.append(&2, B.Ru, a, b), ut, s) : U32}:
  match a:
    case Nil{}:
      u32_zero_l(B.uses.m(b, ut, s))
    case Con{r, +t}:
      match r:
        case B.Ru{+u, +no}:
          %Equal.sym(U32, U32.add(U32.add(B.use.w(u, ut, s), B.uses.m(t, ut, s)), B.uses.m(b, ut, s)),
              U32.add(B.use.w(u, ut, s), U32.add(B.uses.m(t, ut, s), B.uses.m(b, ut, s))), u32_assoc(B.use.w(u, ut, s), B.uses.m(t, ut, s), B.uses.m(b, ut, s))) :
            {_ == U32.add(B.use.w(u, ut, s), B.uses.m(List.append(&2, B.Ru, t, b), ut, s)) : U32}
          %uses_m_app(t, b, ut, s) : {U32.add(B.use.w(u, ut, s), U32.add(B.uses.m(t, ut, s), B.uses.m(b, ut, s))) == U32.add(B.use.w(u, ut, s), _) : U32}
          {==}

def uin_k(h: Bool, +x: U32, +no: U32, +t: List<&2, B.Ru>, +b: List<&2, B.Ru>, +y: U32,
    ih: {List.append(&2, B.Ru, B.uses.in(t, x, y), B.uses.in(b, x, y)) == B.uses.in(List.append(&2, B.Ru, t, b), x, y) : List<&2, B.Ru>}) ->
    {List.append(&2, B.Ru, B.uses.in.k(h, x, no, B.uses.in(t, x, y)), B.uses.in(b, x, y)) == B.uses.in.k(h, x, no, B.uses.in(List.append(&2, B.Ru, t, b), x, y)) : List<&2, B.Ru>}:
  match h:
    case True{}:
      %ih : {Con{B.Ru{x, no}, List.append(&2, B.Ru, B.uses.in(t, x, y), B.uses.in(b, x, y))} == Con{B.Ru{x, no}, _} : List<&2, B.Ru>}
      {==}
    case False{}:
      ih

def uses_in_app(a: List<&2, B.Ru>, +b: List<&2, B.Ru>, +x: U32, +y: U32) ->
    {List.append(&2, B.Ru, B.uses.in(a, x, y), B.uses.in(b, x, y)) == B.uses.in(List.append(&2, B.Ru, a, b), x, y) : List<&2, B.Ru>}:
  match a:
    case Nil{}:
      {==}
    case Con{r, +t}:
      match r:
        case B.Ru{+u, +no}:
          uin_k(U32.is_eq(u, y), x, no, t, b, y, uses_in_app(t, b, x, y))

def umin_k(h: Bool, +x: U32, +no: U32, +t: List<&2, B.Ru>, +y: U32, +ut: B.Ht<B.Un>, +s: B.Ms,
    ih: {wsum(B.uses.in(t, x, y), B.use.w(x, ut, s)) == B.uses.m(B.uses.in(t, x, y), ut, s) : U32}) ->
    {wsum(B.uses.in.k(h, x, no, B.uses.in(t, x, y)), B.use.w(x, ut, s)) == B.uses.m(B.uses.in.k(h, x, no, B.uses.in(t, x, y)), ut, s) : U32}:
  match h:
    case True{}:
      %ih : {U32.add(B.use.w(x, ut, s), wsum(B.uses.in(t, x, y), B.use.w(x, ut, s))) == U32.add(B.use.w(x, ut, s), _) : U32}
      {==}
    case False{}:
      ih

# x's uses, weighed: each by x's weight
def uses_m_in(rs: List<&2, B.Ru>, +x: U32, +y: U32, +ut: B.Ht<B.Un>, +s: B.Ms) ->
    {wsum(B.uses.in(rs, x, y), B.use.w(x, ut, s)) == B.uses.m(B.uses.in(rs, x, y), ut, s) : U32}:
  match rs:
    case Nil{}:
      {==}
    case Con{r, +t}:
      match r:
        case B.Ru{+u, +no}:
          umin_k(U32.is_eq(u, y), x, no, t, y, ut, s, uses_m_in(t, x, y, ut, s))

def reps_zero(n: Nat) -> {reps(n, 0) == 0 : U32}:
  match n:
    case 0n:
      {==}
    case 1n+(+k):
      %Equal.sym(U32, reps(k, 0), 0, reps_zero(k)) : {U32.add(0, _) == 0 : U32}
      u32_zero_r(0)

def wsum_zero(rs: List<&2, B.Ru>) -> {wsum(rs, 0) == 0 : U32}:
  match rs:
    case Nil{}:
      {==}
    case Con{r, +t}:
      %Equal.sym(U32, wsum(t, 0), 0, wsum_zero(t)) : {U32.add(0, _) == 0 : U32}
      u32_zero_r(0)

# a+b and c+d: a+c and b+d
def swap4(+a: U32, +b: U32, +c: U32, +d: U32) -> {U32.add(U32.add(a, b), U32.add(c, d)) == U32.add(U32.add(a, c), U32.add(b, d)) : U32}:
  %Equal.sym(U32, U32.add(U32.add(a, b), U32.add(c, d)), U32.add(a, U32.add(b, U32.add(c, d))), u32_assoc(a, b, U32.add(c, d))) :
    {_ == U32.add(U32.add(a, c), U32.add(b, d)) : U32}
  %u32_assoc(b, c, d) : {U32.add(a, _) == U32.add(U32.add(a, c), U32.add(b, d)) : U32}
  %u32_comm(c, b) : {U32.add(a, U32.add(_, d)) == U32.add(U32.add(a, c), U32.add(b, d)) : U32}
  %Equal.sym(U32, U32.add(U32.add(c, b), d), U32.add(c, U32.add(b, d)), u32_assoc(c, b, d)) : {U32.add(a, _) == U32.add(U32.add(a, c), U32.add(b, d)) : U32}
  Equal.sym(U32, U32.add(U32.add(a, c), U32.add(b, d)), U32.add(a, U32.add(c, U32.add(b, d))), u32_assoc(a, c, U32.add(b, d)))

def reps_add(n: Nat, +a: U32, +b: U32) -> {U32.add(reps(n, a), reps(n, b)) == reps(n, U32.add(a, b)) : U32}:
  match n:
    case 0n:
      u32_zero_r(0)
    case 1n+(+k):
      %reps_add(k, a, b) : {U32.add(U32.add(a, reps(k, a)), U32.add(b, reps(k, b))) == U32.add(U32.add(a, b), _) : U32}
      swap4(a, reps(k, a), b, reps(k, b))

# the sums swapped: each use's c, n times; n times each use's c
def reps_swap(rs: List<&2, B.Ru>, +n: Nat, +c: U32) -> {wsum(rs, reps(n, c)) == reps(n, wsum(rs, c)) : U32}:
  match rs:
    case Nil{}:
      Equal.sym(U32, reps(n, 0), 0, reps_zero(n))
    case Con{r, +t}:
      %reps_add(n, c, wsum(t, c)) : {U32.add(reps(n, c), wsum(t, reps(n, c))) == _ : U32}
      %reps_swap(t, n, c) : {U32.add(reps(n, c), wsum(t, reps(n, c))) == U32.add(reps(n, c), _) : U32}
      {==}

# the wrap law at a modulus m that is 2^32, so that the power is never
# expanded (docs/Proving.md, a big constant)
def wrap_m(+m: Nat, e: {Nat.pow(2n, 32n) == m : Nat}, +a: U32, +b: U32) -> {U32.to_nat(U32.add(a, b)) == Nat.mod(Nat.add(U32.to_nat(a), U32.to_nat(b)), m) : Nat}:
  %e : {U32.to_nat(U32.add(a, b)) == Nat.mod(Nat.add(U32.to_nat(a), U32.to_nat(b)), _) : Nat}
  MU.u32_add_wrap(a, b)

# one, k times: k, mod 2^32
def to_nat_reps(k: Nat, +m: Nat, +e: {Nat.pow(2n, 32n) == m : Nat}) -> {U32.to_nat(reps(k, 1)) == Nat.mod(k, m) : Nat}:
  match k:
    case 0n:
      Equal.sym(Nat, Nat.mod(0n, m), 0n, MNat.zero_mod(m))
    case 1n+(+p):
      %Equal.sym(Nat, U32.to_nat(U32.add(1, reps(p, 1))), Nat.mod(Nat.add(U32.to_nat(1), U32.to_nat(reps(p, 1))), m), wrap_m(m, e, 1, reps(p, 1))) :
        {_ == Nat.mod(1n+p, m) : Nat}
      %Equal.sym(Nat, U32.to_nat(reps(p, 1)), Nat.mod(p, m), to_nat_reps(p, m, e)) : {Nat.mod(Nat.add(1n, _), m) == Nat.mod(1n+p, m) : Nat}
      %MNat.add_comm(Nat.mod(p, m), 1n) : {Nat.mod(_, m) == Nat.mod(1n+p, m) : Nat}
      %Equal.sym(Nat, Nat.mod(Nat.add(Nat.mod(p, m), 1n), m), Nat.mod(Nat.add(p, 1n), m), mod_add_l(p, 1n, m)) : {_ == Nat.mod(1n+p, m) : Nat}
      %MNat.add_comm(p, 1n) : {Nat.mod(Nat.add(p, 1n), m) == Nat.mod(_, m) : Nat}
      {==}

def reps_one_m(+a: U32, +m: Nat, +e: {Nat.pow(2n, 32n) == m : Nat}, h: {Nat.mod(U32.to_nat(a), m) == U32.to_nat(a) : Nat}) ->
    {U32.to_nat(reps(U32.to_nat(a), 1)) == U32.to_nat(a) : Nat}:
  Equal.trans(Nat, U32.to_nat(reps(U32.to_nat(a), 1)), Nat.mod(U32.to_nat(a), m), U32.to_nat(a), to_nat_reps(U32.to_nat(a), m, e), h)

# one, a times: a
def reps_one(+a: U32) -> {reps(U32.to_nat(a), 1) == a : U32}:
  MU.u32_to_nat_inj(reps(U32.to_nat(a), 1), a, reps_one_m(a, Nat.pow(2n, 32n), {==},
    MNat.mod_eq_of_lt(U32.to_nat(a), Nat.pow(2n, 32n), MU.u32_to_nat_lt(a))))

# a call's weight in one copy of an object's unit, and in all a unit's
# copies, as use.w weighs it
def wcv(o0: Bool) -> U32:
  match o0:
    case True{}:
      0
    case False{}:
      1

def uw_k(+o0: Bool, +m: U32) -> U32:
  B.when(U32, o0, v => 0, v => U32.add(1, m))

# a unit's calls, once in each of its copies: each weighed as the
# dispositions weigh a use
def weights(o0: Bool, +m: U32, +rs: List<&2, B.Ru>) -> {reps(1n+U32.to_nat(m), wsum(rs, wcv(o0))) == wsum(rs, uw_k(o0, m)) : U32}:
  match o0:
    case True{}:
      %Equal.sym(U32, wsum(rs, 0), 0, wsum_zero(rs)) : {reps(1n+U32.to_nat(m), _) == _ : U32}
      reps_zero(1n+U32.to_nat(m))
    case False{}:
      %reps_swap(rs, 1n+U32.to_nat(m), 1) : {_ == wsum(rs, U32.add(1, m)) : U32}
      %Equal.sym(U32, reps(U32.to_nat(m), 1), m, reps_one(m)) : {wsum(rs, U32.add(1, _)) == wsum(rs, U32.add(1, m)) : U32}
      {==}

# y's counter in a text built; a call's weight in x's copies
def cy(b: B.Tb, +y: U32) -> U32:
  B.ctr.at(B.tb.ctrs(b), y)

def wx(+e: B.Ec, +x: U32) -> U32:
  wcv(U32.is_eq(B.un.o(B.ec.un(e, x)), 0))

# text put keeps the counters
def tbput_any(b: B.Tb, +xs: List<&2, U32>, +y: U32) -> {cy(b, y) == cy(B.tb.put(b, xs), y) : U32}:
  match b:
    case B.Tb{acc, ctrs}:
      {==}

def mark_k(c: Bool, b: B.Tb, +y: U32) -> {cy(b, y) == cy(B.mark.put.k(c, b), y) : U32}:
  match c:
    case True{}:
      tbput_any(b, [126], y)
    case False{}:
      {==}

def cy_mark(+mark: U32, b: B.Tb, +y: U32) -> {cy(b, y) == cy(B.mark.put(mark, b), y) : U32}:
  mark_k(U32.is_eq(mark, 126), b, y)

# a numbered call counts one on its unit's counter, and none on another's
def next_self(+e: B.Ec, +y: U32, b: B.Tb) -> {U32.add(cy(b, y), 1) == cy(B.ref.next(e, y, b), y) : U32}:
  match b:
    case B.Tb{acc, +ctrs}:
      %Equal.sym(Maybe<&2, U32>, B.um.get(U32, B.um.put(U32, ctrs, y, U32.add(B.ctr.at(ctrs, y), 1)), y),
          mpick(U32, U32.is_eq(y, y), Some{U32.add(B.ctr.at(ctrs, y), 1)}, B.um.get(U32, ctrs, y)),
          um_get_put(U32, ctrs, y, y, U32.add(B.ctr.at(ctrs, y), 1))) :
        {U32.add(B.ctr.at(ctrs, y), 1) == B.ctr.or(_) : U32}
      %Equal.sym(Bool, U32.is_eq(y, y), True{}, u32_is_eq_refl(y)) :
        {U32.add(B.ctr.at(ctrs, y), 1) == B.ctr.or(mpick(U32, _, Some{U32.add(B.ctr.at(ctrs, y), 1)}, B.um.get(U32, ctrs, y))) : U32}
      {==}

def next_other(+e: B.Ec, +y2: U32, +y: U32, b: B.Tb, hq: {U32.is_eq(y2, y) == False{} : Bool}) -> {cy(b, y) == cy(B.ref.next(e, y2, b), y) : U32}:
  match b:
    case B.Tb{acc, +ctrs}:
      %Equal.sym(Maybe<&2, U32>, B.um.get(U32, B.um.put(U32, ctrs, y2, U32.add(B.ctr.at(ctrs, y2), 1)), y),
          mpick(U32, U32.is_eq(y2, y), Some{U32.add(B.ctr.at(ctrs, y2), 1)}, B.um.get(U32, ctrs, y)),
          um_get_put(U32, ctrs, y2, y, U32.add(B.ctr.at(ctrs, y2), 1))) :
        {B.ctr.at(ctrs, y) == B.ctr.or(_) : U32}
      %Equal.sym(Bool, U32.is_eq(y2, y), False{}, hq) :
        {B.ctr.at(ctrs, y) == B.ctr.or(mpick(U32, _, Some{U32.add(B.ctr.at(ctrs, y2), 1)}, B.um.get(U32, ctrs, y))) : U32}
      {==}

# unit.src's and ref.put's decisions mirrored: in the code's file, a
# unit's own lines, and a call by the unit's kind
def us_k(+c: Bool, +e: B.Ec, +x: U32) -> U32:
  B.when(U32, c, u => B.on.maybe(U32, U32, B.ux.find(B.ec.ux(e), B.rf.law(B.un.ref(B.ec.un(e, x)))), v => x, y => y), u => x)

def src_code(+e: B.Ec, hm: {B.ec.mode(e) == 0 : U32}, +x: U32) -> {x == B.unit.src(e, x) : U32}:
  %Equal.sym(U32, B.ec.mode(e), 0, hm) : {x == us_k(Bool.and(U32.is_eq(_, 1), U32.is_eq(B.node.what(B.un.node(B.ec.un(e, x))), 2)), e, x) : U32}
  {==}

def rp_k(+c1: Bool, +c2: Bool, +e: B.Ec, +x: U32, +j: U32, +mark: U32, +r: B.Rf, +y: U32, +b: B.Tb) -> B.Tb:
  B.when(B.Tb, c1,
    u => B.tb.put(B.mark.put(mark, b), List.append(&2, U32, B.codes("Blend_Laws."), B.own.name(e, x, j))),
    u => B.when(B.Tb, c2,
      v => B.tb.put(B.mark.put(mark, b), List.append(&2, U32, B.codes("Blend_Laws."), B.rf.text(B.ec.obs(e), r))),
      v => B.ref.self(U32.is_eq(y, x), e, x, j, y, B.mark.put(mark, b))))

def ref_put_code(+e: B.Ec, hm: {B.ec.mode(e) == 0 : U32}, +x: U32, +j: U32, +mark: U32, +r: B.Rf, +y: U32, +b: B.Tb) ->
    {B.ref.self(U32.is_eq(y, x), e, x, j, y, B.mark.put(mark, b)) == B.ref.put(e, x, j, mark, r, Some{y}, b) : B.Tb}:
  %Equal.sym(U32, B.ec.mode(e), 0, hm) :
    {B.ref.self(U32.is_eq(y, x), e, x, j, y, B.mark.put(mark, b)) ==
      rp_k(Bool.and(U32.is_eq(_, 2), B.proves.own(B.ec.ut(e), x, y)),
        Bool.and(U32.is_eq(_, 2), Bool.or(U32.is_eq(B.node.what(B.un.node(B.ec.un(e, y))), 1), U32.is_eq(B.node.what(B.un.node(B.ec.un(e, y))), 2))),
        e, x, j, mark, r, y, b) : B.Tb}
  {==}

def refput_none(+e: B.Ec, +x: U32, +j: U32, +mark: U32, +r: B.Rf, +b: B.Tb, +y: U32) -> {cy(b, y) == cy(B.ref.put(e, x, j, mark, r, None{}, b), y) : U32}:
  Equal.trans(U32, cy(b, y), cy(B.mark.put(mark, b), y), cy(B.ref.put(e, x, j, mark, r, None{}, b), y), cy_mark(mark, b, y),
    tbput_any(B.mark.put(mark, b), B.when(List<&2, U32>, Bool.and(U32.is_gt(B.ec.mode(e), 0), U32.is_eq(B.loc.mod(B.ob.no(B.ob.at(B.ec.obs(e), B.rf.obj(r)))), 0)),
      u => List.append(&2, U32, B.codes("Blend_0."), B.rf.text(B.ec.obs(e), r)), u => B.rf.ext(e, r)), y))

# a text whose counter is b's: the rest of a body written after it, as
# after b
def keep(+b1: B.Tb, +b: B.Tb, +r: List<&2, B.Rt>, +e: B.Ec, +x: U32, +j: U32, +y: U32, +w: U32, h: {cy(b, y) == cy(b1, y) : U32},
    ih: {cy(B.rts.put(r, e, x, j, b1), y) == U32.add(cy(b1, y), w) : U32}) -> {cy(B.rts.put(r, e, x, j, b1), y) == U32.add(cy(b, y), w) : U32}:
  %Equal.sym(U32, cy(b, y), cy(b1, y), h) : {cy(B.rts.put(r, e, x, j, b1), y) == U32.add(_, w) : U32}
  ih

def rk_k(+o0: Bool, +e: B.Ec, +y: U32, +b: B.Tb) -> B.Tb:
  B.when(B.Tb, o0, u => B.tb.put(b, B.unit.text(e, y)), u => B.ref.next(e, y, b))

def rk_other(o0: Bool, +e: B.Ec, +y2: U32, +b: B.Tb, +y: U32, hq: {U32.is_eq(y2, y) == False{} : Bool}) -> {cy(b, y) == cy(rk_k(o0, e, y2, b), y) : U32}:
  match o0:
    case True{}:
      tbput_any(b, B.unit.text(e, y2), y)
    case False{}:
      next_other(e, y2, y, b, hq)

# a call to another unit than y leaves y's counter
def kind_other(p0: Bool, p1: Bool, +e: B.Ec, +x: U32, +y2: U32, +j: U32, +b: B.Tb, +y: U32, hq: {U32.is_eq(y2, y) == False{} : Bool}) ->
    {cy(b, y) == cy(B.ref.kind.k(p0, p1, e, x, y2, j, b), y) : U32}:
  match p0 p1:
    case True{} _:
      tbput_any(b, B.unit.text(e, y2), y)
    case False{} True{}:
      rk_other(U32.is_eq(B.un.o(B.ec.un(e, x)), 0), e, y2, b, y, hq)
    case False{} False{}:
      tbput_any(b, B.own.name(e, y2, j), y)

# a call to y, a copied unit: one more on its counter where the writer
# is an object's, none where it is a module's definition
def o_step(o0: Bool, +e: B.Ec, +x: U32, +y: U32, +j: U32, +b2: B.Tb, +b: B.Tb, +r: List<&2, B.Rt>, +w: U32, +hb: {cy(b, y) == cy(b2, y) : U32},
    ih: @c:B.Tb -> {cy(B.rts.put(r, e, x, j, c), y) == U32.add(cy(c, y), w) : U32}) ->
    {cy(B.rts.put(r, e, x, j, rk_k(o0, e, y, b2)), y) == U32.add(cy(b, y), U32.add(wcv(o0), w)) : U32}:
  match o0:
    case True{}:
      %Equal.sym(U32, U32.add(0, w), w, u32_zero_l(w)) : {cy(B.rts.put(r, e, x, j, B.tb.put(b2, B.unit.text(e, y))), y) == U32.add(cy(b, y), _) : U32}
      keep(B.tb.put(b2, B.unit.text(e, y)), b, r, e, x, j, y, w,
        Equal.trans(U32, cy(b, y), cy(b2, y), cy(B.tb.put(b2, B.unit.text(e, y)), y), hb, tbput_any(b2, B.unit.text(e, y), y)), ih(B.tb.put(b2, B.unit.text(e, y))))
    case False{}:
      %u32_assoc(cy(b, y), 1, w) : {cy(B.rts.put(r, e, x, j, B.ref.next(e, y, b2)), y) == _ : U32}
      %Equal.sym(U32, cy(b, y), cy(b2, y), hb) : {cy(B.rts.put(r, e, x, j, B.ref.next(e, y, b2)), y) == U32.add(U32.add(_, 1), w) : U32}
      %Equal.sym(U32, U32.add(cy(b2, y), 1), cy(B.ref.next(e, y, b2), y), next_self(e, y, b2)) : {cy(B.rts.put(r, e, x, j, B.ref.next(e, y, b2)), y) == U32.add(_, w) : U32}
      ih(B.ref.next(e, y, b2))

def target_step(q: Bool, +y2: U32, +e: B.Ec, +x: U32, +j: U32, +b2: B.Tb, +b: B.Tb, +r: List<&2, B.Rt>, +no: U32, +y: U32,
    +hk: {B.mu.kind(B.ec.mu(e, y)) == 1 : U32}, eq: {q == U32.is_eq(y2, y) : Bool}, +hb: {cy(b, y) == cy(b2, y) : U32},
    ih: @c:B.Tb -> {cy(B.rts.put(r, e, x, j, c), y) == U32.add(cy(c, y), wsum(B.uses.in(B.refs.rts(r, B.ec.ux(e), x, no), x, y), wx(e, x))) : U32}) ->
    {cy(B.rts.put(r, e, x, j, B.ref.kind.k(U32.is_eq(B.mu.kind(B.ec.mu(e, y2)), 0), U32.is_eq(B.mu.kind(B.ec.mu(e, y2)), 1), e, x, y2, j, b2)), y) ==
      U32.add(cy(b, y), wsum(B.uses.in.k(q, x, no, B.uses.in(B.refs.rts(r, B.ec.ux(e), x, no), x, y)), wx(e, x))) : U32}:
  match q:
    case True{}:
      %Equal.sym(U32, y2, y, u32_eq_of_is_eq(y2, y, Equal.sym(Bool, True{}, U32.is_eq(y2, y), eq))) :
        {cy(B.rts.put(r, e, x, j, B.ref.kind.k(U32.is_eq(B.mu.kind(B.ec.mu(e, _)), 0), U32.is_eq(B.mu.kind(B.ec.mu(e, _)), 1), e, x, _, j, b2)), y) ==
          U32.add(cy(b, y), wsum(B.uses.in.k(True{}, x, no, B.uses.in(B.refs.rts(r, B.ec.ux(e), x, no), x, y)), wx(e, x))) : U32}
      %Equal.sym(U32, B.mu.kind(B.ec.mu(e, y)), 1, hk) :
        {cy(B.rts.put(r, e, x, j, B.ref.kind.k(U32.is_eq(_, 0), U32.is_eq(_, 1), e, x, y, j, b2)), y) ==
          U32.add(cy(b, y), wsum(B.uses.in.k(True{}, x, no, B.uses.in(B.refs.rts(r, B.ec.ux(e), x, no), x, y)), wx(e, x))) : U32}
      o_step(U32.is_eq(B.un.o(B.ec.un(e, x)), 0), e, x, y, j, b2, b, r, wsum(B.uses.in(B.refs.rts(r, B.ec.ux(e), x, no), x, y), wx(e, x)), hb, ih)
    case False{}:
      keep(B.ref.kind.k(U32.is_eq(B.mu.kind(B.ec.mu(e, y2)), 0), U32.is_eq(B.mu.kind(B.ec.mu(e, y2)), 1), e, x, y2, j, b2), b, r, e, x, j, y, wsum(B.uses.in(B.refs.rts(r, B.ec.ux(e), x, no), x, y), wx(e, x)),
        Equal.trans(U32, cy(b, y), cy(b2, y), cy(B.ref.kind.k(U32.is_eq(B.mu.kind(B.ec.mu(e, y2)), 0), U32.is_eq(B.mu.kind(B.ec.mu(e, y2)), 1), e, x, y2, j, b2), y), hb,
          kind_other(U32.is_eq(B.mu.kind(B.ec.mu(e, y2)), 0), U32.is_eq(B.mu.kind(B.ec.mu(e, y2)), 1), e, x, y2, j, b2, y, Equal.sym(Bool, False{}, U32.is_eq(y2, y), eq))),
        ih(B.ref.kind.k(U32.is_eq(B.mu.kind(B.ec.mu(e, y2)), 0), U32.is_eq(B.mu.kind(B.ec.mu(e, y2)), 1), e, x, y2, j, b2)))

# refs.rts's step mirrored: a call to the unit itself aside
def rs_k(+s: Bool, +y2: U32, +r: List<&2, B.Rt>, +ux: B.Ht<B.Xe>, +self: U32, +no: U32) -> List<&2, B.Ru>:
  B.when(List<&2, B.Ru>, s, v => B.refs.rts(r, ux, self, no), v => Con{B.Ru{y2, no}, B.refs.rts(r, ux, self, no)})

def self_step(s: Bool, +y2: U32, +mark: U32, +r: List<&2, B.Rt>, +e: B.Ec, +x: U32, +j: U32, +b: B.Tb, +y: U32, +no: U32,
    +hk: {B.mu.kind(B.ec.mu(e, y)) == 1 : U32}, ih: @c:B.Tb -> {cy(B.rts.put(r, e, x, j, c), y) == U32.add(cy(c, y), wsum(B.uses.in(B.refs.rts(r, B.ec.ux(e), x, no), x, y), wx(e, x))) : U32}) ->
    {cy(B.rts.put(r, e, x, j, B.ref.self(s, e, x, j, y2, B.mark.put(mark, b))), y) == U32.add(cy(b, y), wsum(B.uses.in(rs_k(s, y2, r, B.ec.ux(e), x, no), x, y), wx(e, x))) : U32}:
  match s:
    case True{}:
      keep(B.tb.put(B.mark.put(mark, b), B.own.name(e, x, j)), b, r, e, x, j, y, wsum(B.uses.in(B.refs.rts(r, B.ec.ux(e), x, no), x, y), wx(e, x)),
        Equal.trans(U32, cy(b, y), cy(B.mark.put(mark, b), y), cy(B.tb.put(B.mark.put(mark, b), B.own.name(e, x, j)), y), cy_mark(mark, b, y),
          tbput_any(B.mark.put(mark, b), B.own.name(e, x, j), y)), ih(B.tb.put(B.mark.put(mark, b), B.own.name(e, x, j))))
    case False{}:
      target_step(U32.is_eq(y2, y), y2, e, x, j, B.mark.put(mark, b), b, r, no, y, hk, {==}, cy_mark(mark, b, y), ih)

def rr_k(+mb: Maybe<&2, U32>, +r: List<&2, B.Rt>, +ux: B.Ht<B.Xe>, +self: U32, +no: U32) -> List<&2, B.Ru>:
  B.on.maybe(U32, List<&2, B.Ru>, mb, v => B.refs.rts(r, ux, self, no),
    +x => B.when(List<&2, B.Ru>, U32.is_eq(x, self), v => B.refs.rts(r, ux, self, no), v => Con{B.Ru{x, no}, B.refs.rts(r, ux, self, no)}))

def rr_step(mb: Maybe<&2, U32>, +mark: U32, +ref: B.Rf, +r: List<&2, B.Rt>, +e: B.Ec, +x: U32, +j: U32, +b: B.Tb, +y: U32, +no: U32,
    +hm: {B.ec.mode(e) == 0 : U32}, +hk: {B.mu.kind(B.ec.mu(e, y)) == 1 : U32},
    ih: @c:B.Tb -> {cy(B.rts.put(r, e, x, j, c), y) == U32.add(cy(c, y), wsum(B.uses.in(B.refs.rts(r, B.ec.ux(e), x, no), x, y), wx(e, x))) : U32}) ->
    {cy(B.rts.put(r, e, x, j, B.ref.put(e, x, j, mark, ref, mb, b)), y) == U32.add(cy(b, y), wsum(B.uses.in(rr_k(mb, r, B.ec.ux(e), x, no), x, y), wx(e, x))) : U32}:
  match mb:
    case None{}:
      keep(B.ref.put(e, x, j, mark, ref, None{}, b), b, r, e, x, j, y, wsum(B.uses.in(B.refs.rts(r, B.ec.ux(e), x, no), x, y), wx(e, x)), refput_none(e, x, j, mark, ref, b, y), ih(B.ref.put(e, x, j, mark, ref, None{}, b)))
    case Some{+y2}:
      %ref_put_code(e, hm, x, j, mark, ref, y2, b) :
        {cy(B.rts.put(r, e, x, j, _), y) == U32.add(cy(b, y), wsum(B.uses.in(rr_k(Some{y2}, r, B.ec.ux(e), x, no), x, y), wx(e, x))) : U32}
      self_step(U32.is_eq(y2, x), y2, mark, r, e, x, j, b, y, no, hk, ih)

# a body's tokens written: y's counter up by x's calls to it, each
# weighed as one copy of x weighs it
def rts_cy(ts: List<&2, B.Rt>, +e: B.Ec, +x: U32, +j: U32, +b: B.Tb, +y: U32, +no: U32, +hm: {B.ec.mode(e) == 0 : U32},
    +hk: {B.mu.kind(B.ec.mu(e, y)) == 1 : U32}) ->
    {cy(B.rts.put(ts, e, x, j, b), y) == U32.add(cy(b, y), wsum(B.uses.in(B.refs.rts(ts, B.ec.ux(e), x, no), x, y), wx(e, x))) : U32}:
  match ts:
    case Nil{}:
      Equal.sym(U32, U32.add(cy(b, y), 0), cy(b, y), u32_zero_r(cy(b, y)))
    case Con{t, +r}:
      match t:
        case B.RT{+tk}:
          keep(B.tb.put(b, B.tok.in.proof(e, tk)), b, r, e, x, j, y, wsum(B.uses.in(B.refs.rts(r, B.ec.ux(e), x, no), x, y), wx(e, x)), tbput_any(b, B.tok.in.proof(e, tk), y),
            rts_cy(r, e, x, j, B.tb.put(b, B.tok.in.proof(e, tk)), y, no, hm, hk))
        case B.RR{+mark, +ref}:
          rr_step(B.ux.find(B.ec.ux(e), ref), mark, ref, r, e, x, j, b, y, no, hm, hk, c => rts_cy(r, e, x, j, c, y, no, hm, hk))
        case B.RX{+mark, +path, +rest}:
          keep(B.tb.put(B.mark.put(mark, b), List.append(&2, U32, B.alias.of(e, path), Con{46, rest})), b, r, e, x, j, y, wsum(B.uses.in(B.refs.rts(r, B.ec.ux(e), x, no), x, y), wx(e, x)),
            Equal.trans(U32, cy(b, y), cy(B.mark.put(mark, b), y), cy(B.tb.put(B.mark.put(mark, b), List.append(&2, U32, B.alias.of(e, path), Con{46, rest})), y),
              cy_mark(mark, b, y), tbput_any(B.mark.put(mark, b), List.append(&2, U32, B.alias.of(e, path), Con{46, rest}), y)),
            rts_cy(r, e, x, j, B.tb.put(B.mark.put(mark, b), List.append(&2, U32, B.alias.of(e, path), Con{46, rest})), y, no, hm, hk))

# rl.put's start of a line mirrored: a space, or a newline and the
# indentation, neither a call
def wb_k(+c: Bool, +b: B.Tb, +ind: U32, +dind: U32) -> B.Tb:
  B.when(B.Tb, c, u => B.tb.put(b, [32]),
    u => B.tb.put(b, Con{10, B.spaces(U32.to_nat(B.when(U32, U32.is_gt(ind, dind), v => U32.sub(ind, dind), v => 0)))}))

def cy_wb(c: Bool, +b: B.Tb, +ind: U32, +dind: U32, +y: U32) -> {cy(b, y) == cy(wb_k(c, b, ind, dind), y) : U32}:
  match c:
    case True{}:
      tbput_any(b, [32], y)
    case False{}:
      tbput_any(b, Con{10, B.spaces(U32.to_nat(B.when(U32, U32.is_gt(ind, dind), v => U32.sub(ind, dind), v => 0)))}, y)

def keep_l(+b1: B.Tb, +b: B.Tb, +t: List<&2, B.Rl>, +e: B.Ec, +x: U32, +j: U32, +dind: U32, +y: U32, +w: U32, h: {cy(b, y) == cy(b1, y) : U32},
    ih: {cy(B.rls.put(t, e, x, j, dind, b1), y) == U32.add(cy(b1, y), w) : U32}) -> {cy(B.rls.put(t, e, x, j, dind, b1), y) == U32.add(cy(b, y), w) : U32}:
  %Equal.sym(U32, cy(b, y), cy(b1, y), h) : {cy(B.rls.put(t, e, x, j, dind, b1), y) == U32.add(_, w) : U32}
  ih

# a body's lines written: y's counter up by their calls to it
def rls_cy(ls: List<&2, B.Rl>, +e: B.Ec, +x: U32, +j: U32, +dind: U32, +b: B.Tb, +y: U32, +hm: {B.ec.mode(e) == 0 : U32},
    +hk: {B.mu.kind(B.ec.mu(e, y)) == 1 : U32}) ->
    {cy(B.rls.put(ls, e, x, j, dind, b), y) == U32.add(cy(b, y), wsum(B.uses.in(B.refs.rls(ls, B.ec.ux(e), x), x, y), wx(e, x))) : U32}:
  match ls:
    case Nil{}:
      Equal.sym(U32, U32.add(cy(b, y), 0), cy(b, y), u32_zero_r(cy(b, y)))
    case Con{l, +t}:
      match l:
        case B.Rl{+no, +ind, ts}:
          match ts:
            case Nil{}:
              keep_l(B.tb.put(b, [10]), b, t, e, x, j, dind, y, wsum(B.uses.in(B.refs.rls(t, B.ec.ux(e), x), x, y), wx(e, x)), tbput_any(b, [10], y),
                rls_cy(t, e, x, j, dind, B.tb.put(b, [10]), y, hm, hk))
            case Con{+tk, +r}:
              %uses_in_app(B.refs.rts(Con{tk, r}, B.ec.ux(e), x, no), B.refs.rls(t, B.ec.ux(e), x), x, y) :
                {cy(B.rls.put(t, e, x, j, dind, B.rts.put(Con{tk, r}, e, x, j, wb_k(U32.is_eq(no, B.node.no(B.un.node(B.ec.un(e, x)))), b, ind, dind))), y) ==
                  U32.add(cy(b, y), wsum(_, wx(e, x))) : U32}
              %wsum_app(B.uses.in(B.refs.rts(Con{tk, r}, B.ec.ux(e), x, no), x, y), B.uses.in(B.refs.rls(t, B.ec.ux(e), x), x, y), wx(e, x)) :
                {cy(B.rls.put(t, e, x, j, dind, B.rts.put(Con{tk, r}, e, x, j, wb_k(U32.is_eq(no, B.node.no(B.un.node(B.ec.un(e, x)))), b, ind, dind))), y) ==
                  U32.add(cy(b, y), _) : U32}
              %u32_assoc(cy(b, y), wsum(B.uses.in(B.refs.rts(Con{tk, r}, B.ec.ux(e), x, no), x, y), wx(e, x)), wsum(B.uses.in(B.refs.rls(t, B.ec.ux(e), x), x, y), wx(e, x))) :
                {cy(B.rls.put(t, e, x, j, dind, B.rts.put(Con{tk, r}, e, x, j, wb_k(U32.is_eq(no, B.node.no(B.un.node(B.ec.un(e, x)))), b, ind, dind))), y) == _ : U32}
              %Equal.sym(U32, cy(b, y), cy(wb_k(U32.is_eq(no, B.node.no(B.un.node(B.ec.un(e, x)))), b, ind, dind), y), cy_wb(U32.is_eq(no, B.node.no(B.un.node(B.ec.un(e, x)))), b, ind, dind, y)) :
                {cy(B.rls.put(t, e, x, j, dind, B.rts.put(Con{tk, r}, e, x, j, wb_k(U32.is_eq(no, B.node.no(B.un.node(B.ec.un(e, x)))), b, ind, dind))), y) ==
                  U32.add(U32.add(_, wsum(B.uses.in(B.refs.rts(Con{tk, r}, B.ec.ux(e), x, no), x, y), wx(e, x))), wsum(B.uses.in(B.refs.rls(t, B.ec.ux(e), x), x, y), wx(e, x))) : U32}
              %rts_cy(Con{tk, r}, e, x, j, wb_k(U32.is_eq(no, B.node.no(B.un.node(B.ec.un(e, x)))), b, ind, dind), y, no, hm, hk) :
                {cy(B.rls.put(t, e, x, j, dind, B.rts.put(Con{tk, r}, e, x, j, wb_k(U32.is_eq(no, B.node.no(B.un.node(B.ec.un(e, x)))), b, ind, dind))), y) ==
                  U32.add(_, wsum(B.uses.in(B.refs.rls(t, B.ec.ux(e), x), x, y), wx(e, x))) : U32}
              rls_cy(t, e, x, j, dind, B.rts.put(Con{tk, r}, e, x, j, wb_k(U32.is_eq(no, B.node.no(B.un.node(B.ec.un(e, x)))), b, ind, dind)), y, hm, hk)

# a unit's copy written, in its parts: the text before its body, its
# header written, its lines
def t0(+e: B.Ec, +x: U32, +j: U32, +b: B.Tb) -> B.Tb:
  B.tb.put(b, List.append(&2, U32, B.marker(e, x), List.append(&2, U32, B.unit.kw(e, x), B.own.name(e, x, j))))

def hd_w(+e: B.Ec, +x: U32, +j: U32, +b: B.Tb) -> B.Tb:
  B.rts.put(B.un.hd(B.ec.un(e, x)), e, x, j, t0(e, x, j, b))

def ln_w(+e: B.Ec, +x: U32, +j: U32, +b: B.Tb) -> B.Tb:
  B.rls.put(B.un.lines(B.ec.un(e, x)), e, x, j, B.node.ind(B.un.node(B.ec.un(e, x))), hd_w(e, x, j, b))

def hd_u(+e: B.Ec, +x: U32, +y: U32) -> List<&2, B.Ru>:
  B.uses.in(B.refs.rts(B.un.hd(B.ec.un(e, x)), B.ec.ux(e), x, B.node.no(B.un.node(B.ec.un(e, x)))), x, y)

def ln_u(+e: B.Ec, +x: U32, +y: U32) -> List<&2, B.Ru>:
  B.uses.in(B.refs.rls(B.un.lines(B.ec.un(e, x)), B.ec.ux(e), x), x, y)

# one copy of x written: y's counter up by x's calls to it
def unit_cy(+e: B.Ec, +x: U32, +j: U32, +b: B.Tb, +y: U32, +hm: {B.ec.mode(e) == 0 : U32}, +hk: {B.mu.kind(B.ec.mu(e, y)) == 1 : U32}) ->
    {cy(B.unit.put(e, x, j, b), y) == U32.add(cy(b, y), wsum(B.uses.in(B.uses.e(e, x), x, y), wx(e, x))) : U32}:
  %src_code(e, hm, x) : {cy(B.unit.put.as(e, _, x, j, b), y) == U32.add(cy(b, y), wsum(B.uses.in(B.uses.e(e, x), x, y), wx(e, x))) : U32}
  %uses_in_app(B.refs.rts(B.un.hd(B.ec.un(e, x)), B.ec.ux(e), x, B.node.no(B.un.node(B.ec.un(e, x)))), B.refs.rls(B.un.lines(B.ec.un(e, x)), B.ec.ux(e), x), x, y) :
    {cy(B.tb.put(ln_w(e, x, j, b), List.append(&2, U32, B.witness.body(e, x), [10])), y) == U32.add(cy(b, y), wsum(_, wx(e, x))) : U32}
  %wsum_app(hd_u(e, x, y), ln_u(e, x, y), wx(e, x)) :
    {cy(B.tb.put(ln_w(e, x, j, b), List.append(&2, U32, B.witness.body(e, x), [10])), y) == U32.add(cy(b, y), _) : U32}
  %u32_assoc(cy(b, y), wsum(hd_u(e, x, y), wx(e, x)), wsum(ln_u(e, x, y), wx(e, x))) :
    {cy(B.tb.put(ln_w(e, x, j, b), List.append(&2, U32, B.witness.body(e, x), [10])), y) == _ : U32}
  %Equal.sym(U32, cy(b, y), cy(t0(e, x, j, b), y), tbput_any(b, List.append(&2, U32, B.marker(e, x), List.append(&2, U32, B.unit.kw(e, x), B.own.name(e, x, j))), y)) :
    {cy(B.tb.put(ln_w(e, x, j, b), List.append(&2, U32, B.witness.body(e, x), [10])), y) ==
      U32.add(U32.add(_, wsum(hd_u(e, x, y), wx(e, x))), wsum(ln_u(e, x, y), wx(e, x))) : U32}
  %rts_cy(B.un.hd(B.ec.un(e, x)), e, x, j, t0(e, x, j, b), y, B.node.no(B.un.node(B.ec.un(e, x))), hm, hk) :
    {cy(B.tb.put(ln_w(e, x, j, b), List.append(&2, U32, B.witness.body(e, x), [10])), y) == U32.add(_, wsum(ln_u(e, x, y), wx(e, x))) : U32}
  %rls_cy(B.un.lines(B.ec.un(e, x)), e, x, j, B.node.ind(B.un.node(B.ec.un(e, x))), hd_w(e, x, j, b), y, hm, hk) :
    {cy(B.tb.put(ln_w(e, x, j, b), List.append(&2, U32, B.witness.body(e, x), [10])), y) == _ : U32}
  Equal.sym(U32, cy(ln_w(e, x, j, b), y), cy(B.tb.put(ln_w(e, x, j, b), List.append(&2, U32, B.witness.body(e, x), [10])), y),
    tbput_any(ln_w(e, x, j, b), List.append(&2, U32, B.witness.body(e, x), [10]), y))

def cx(+e: B.Ec, +x: U32, +y: U32) -> U32:
  wsum(B.uses.in(B.uses.e(e, x), x, y), wx(e, x))

# n more copies of x: x's calls, n times
def copies_cy(n: Nat, +e: B.Ec, +x: U32, +j: U32, +b: B.Tb, +y: U32, +hm: {B.ec.mode(e) == 0 : U32}, +hk: {B.mu.kind(B.ec.mu(e, y)) == 1 : U32}) ->
    {cy(B.copies.put(n, e, x, j, b), y) == U32.add(cy(b, y), reps(n, cx(e, x, y))) : U32}:
  match n:
    case 0n:
      Equal.sym(U32, U32.add(cy(b, y), 0), cy(b, y), u32_zero_r(cy(b, y)))
    case 1n+(+k):
      %u32_assoc(cy(b, y), cx(e, x, y), reps(k, cx(e, x, y))) : {cy(B.copies.put(k, e, x, U32.add(j, 1), B.unit.put(e, x, j, b)), y) == _ : U32}
      %unit_cy(e, x, j, b, y, hm, hk) : {cy(B.copies.put(k, e, x, U32.add(j, 1), B.unit.put(e, x, j, b)), y) == U32.add(_, reps(k, cx(e, x, y))) : U32}
      copies_cy(k, e, x, U32.add(j, 1), B.unit.put(e, x, j, b), y, hm, hk)

# all of x's copies, its own name's and its numbered ones
def all_cy(+e: B.Ec, +x: U32, mu: B.Mu, +b: B.Tb, +y: U32, +hm: {B.ec.mode(e) == 0 : U32}, +hk: {B.mu.kind(B.ec.mu(e, y)) == 1 : U32}) ->
    {cy(B.unit.all(e, x, mu, b), y) == U32.add(cy(b, y), reps(1n+U32.to_nat(B.mu.m(mu)), cx(e, x, y))) : U32}:
  match mu:
    case B.Mu{+m, +kind}:
      %u32_assoc(cy(b, y), cx(e, x, y), reps(U32.to_nat(m), cx(e, x, y))) : {cy(B.copies.put(U32.to_nat(m), e, x, 1, B.unit.put(e, x, 0, b)), y) == _ : U32}
      %unit_cy(e, x, 0, b, y, hm, hk) : {cy(B.copies.put(U32.to_nat(m), e, x, 1, B.unit.put(e, x, 0, b)), y) == U32.add(_, reps(U32.to_nat(m), cx(e, x, y))) : U32}
      copies_cy(U32.to_nat(m), e, x, 1, B.unit.put(e, x, 0, b), y, hm, hk)

# what the writer reads of a unit and of its disposition, as use.w reads
# them
def un_e(e: B.Ec, +x: U32) -> {B.ec.un(e, x) == B.ut.un(B.ec.ut(e), x) : B.Un}:
  match e:
    case B.Ec{files, obs, us, als, own, res, paths, +mode, rtypes, ux, ut, mt}:
      {==}

def mu_e(e: B.Ec, +x: U32) -> {B.ec.mu(e, x) == B.ms.mu(B.ec.ms(e), x) : B.Mu}:
  match e:
    case B.Ec{files, obs, us, als, own, res, paths, +mode, rtypes, ux, ut, mt}:
      {==}

# an order written: y's counter up by each unit's calls to it, weighed as
# the dispositions weigh them
def order_cy(xs: List<&2, U32>, +e: B.Ec, +b: B.Tb, +y: U32, +hm: {B.ec.mode(e) == 0 : U32}, +hk: {B.mu.kind(B.ec.mu(e, y)) == 1 : U32}) ->
    {cy(B.order.put(xs, e, b), y) == U32.add(cy(b, y), B.uses.m(B.uses.of.e(xs, e, y), B.ec.ut(e), B.ec.ms(e))) : U32}:
  match xs:
    case Nil{}:
      Equal.sym(U32, U32.add(cy(b, y), 0), cy(b, y), u32_zero_r(cy(b, y)))
    case Con{+x, +t}:
      %uses_m_app(B.uses.in(B.uses.e(e, x), x, y), B.uses.of.e(t, e, y), B.ec.ut(e), B.ec.ms(e)) : {cy(B.order.put(t, e, B.unit.all(e, x, B.ec.mu(e, x), b)), y) == U32.add(cy(b, y), _) : U32}
      %u32_assoc(cy(b, y), B.uses.m(B.uses.in(B.uses.e(e, x), x, y), B.ec.ut(e), B.ec.ms(e)), B.uses.m(B.uses.of.e(t, e, y), B.ec.ut(e), B.ec.ms(e))) : {cy(B.order.put(t, e, B.unit.all(e, x, B.ec.mu(e, x), b)), y) == _ : U32}
      %uses_m_in(B.uses.e(e, x), x, y, B.ec.ut(e), B.ec.ms(e)) : {cy(B.order.put(t, e, B.unit.all(e, x, B.ec.mu(e, x), b)), y) == U32.add(U32.add(cy(b, y), _), B.uses.m(B.uses.of.e(t, e, y), B.ec.ut(e), B.ec.ms(e))) : U32}
      %un_e(e, x) :
        {cy(B.order.put(t, e, B.unit.all(e, x, B.ec.mu(e, x), b)), y) == U32.add(U32.add(cy(b, y), wsum(B.uses.in(B.uses.e(e, x), x, y), uw_k(U32.is_eq(B.un.o(_), 0), B.mu.m(B.ms.mu(B.ec.ms(e), x))))), B.uses.m(B.uses.of.e(t, e, y), B.ec.ut(e), B.ec.ms(e))) : U32}
      %mu_e(e, x) :
        {cy(B.order.put(t, e, B.unit.all(e, x, B.ec.mu(e, x), b)), y) == U32.add(U32.add(cy(b, y), wsum(B.uses.in(B.uses.e(e, x), x, y), uw_k(U32.is_eq(B.un.o(B.ec.un(e, x)), 0), B.mu.m(_)))), B.uses.m(B.uses.of.e(t, e, y), B.ec.ut(e), B.ec.ms(e))) : U32}
      %weights(U32.is_eq(B.un.o(B.ec.un(e, x)), 0), B.mu.m(B.ec.mu(e, x)), B.uses.in(B.uses.e(e, x), x, y)) :
        {cy(B.order.put(t, e, B.unit.all(e, x, B.ec.mu(e, x), b)), y) == U32.add(U32.add(cy(b, y), _), B.uses.m(B.uses.of.e(t, e, y), B.ec.ut(e), B.ec.ms(e))) : U32}
      %all_cy(e, x, B.ec.mu(e, x), b, y, hm, hk) : {cy(B.order.put(t, e, B.unit.all(e, x, B.ec.mu(e, x), b)), y) == U32.add(_, B.uses.m(B.uses.of.e(t, e, y), B.ec.ut(e), B.ec.ms(e))) : U32}
      order_cy(t, e, B.unit.all(e, x, B.ec.mu(e, x), b), y, hm, hk)

def Laws.sharing.counts(xs, e, b, y, hm, hk):
  order_cy(xs, e, b, y, hm, hk)

# The final dispositions
# ----------------------
#
# A unit's disposition is set at its turn and at no other (`frozen`, the
# order holding it once); a copied unit's users come before it, and none
# after (`at_turn`), so that what its turn read of theirs is final
# (`um_frozen`).

def ms_set_self(s: B.Ms, +x: U32, +mu: B.Mu) -> {mu == B.ms.mu(B.ms.set(s, x, mu), x) : B.Mu}:
  match s:
    case B.Ms{+ms, ers}:
      %Equal.sym(Maybe<&2, B.Mu>, B.um.get(B.Mu, B.um.put(B.Mu, ms, x, mu), x), mpick(B.Mu, U32.is_eq(x, x), Some{mu}, B.um.get(B.Mu, ms, x)), um_get_put(B.Mu, ms, x, x, mu)) :
        {mu == B.mu.or(_) : B.Mu}
      %Equal.sym(Bool, U32.is_eq(x, x), True{}, u32_is_eq_refl(x)) : {mu == B.mu.or(mpick(B.Mu, _, Some{mu}, B.um.get(B.Mu, ms, x))) : B.Mu}
      {==}

def ms_set_other(s: B.Ms, +x: U32, +mu: B.Mu, +z: U32, hq: {U32.is_eq(x, z) == False{} : Bool}) -> {B.ms.mu(s, z) == B.ms.mu(B.ms.set(s, x, mu), z) : B.Mu}:
  match s:
    case B.Ms{+ms, ers}:
      %Equal.sym(Maybe<&2, B.Mu>, B.um.get(B.Mu, B.um.put(B.Mu, ms, x, mu), z), mpick(B.Mu, U32.is_eq(x, z), Some{mu}, B.um.get(B.Mu, ms, z)), um_get_put(B.Mu, ms, x, z, mu)) :
        {B.mu.or(B.um.get(B.Mu, ms, z)) == B.mu.or(_) : B.Mu}
      %Equal.sym(Bool, U32.is_eq(x, z), False{}, hq) : {B.mu.or(B.um.get(B.Mu, ms, z)) == B.mu.or(mpick(B.Mu, _, Some{mu}, B.um.get(B.Mu, ms, z))) : B.Mu}
      {==}

def ms_er(s: B.Ms, +e: B.Er, +z: U32) -> {B.ms.mu(s, z) == B.ms.mu(B.ms.er(s, e), z) : B.Mu}:
  match s:
    case B.Ms{ms, ers}:
      {==}

# mult.aff's one use mirrored
def ak(+c: Bool, +s: B.Ms, +x: U32, +rs: List<&2, B.Ru>) -> B.Ms:
  B.when(B.Ms, c, v => B.ms.set(s, x, B.Mu{B.mu.m(B.ms.mu(s, B.ru.user(rs))), 2}), v => s)

def aff_k(c: Bool, +s: B.Ms, +x: U32, +rs: List<&2, B.Ru>, +z: U32, hq: {U32.is_eq(x, z) == False{} : Bool}) -> {B.ms.mu(s, z) == B.ms.mu(ak(c, s, x, rs), z) : B.Mu}:
  match c:
    case True{}:
      ms_set_other(s, x, B.Mu{B.mu.m(B.ms.mu(s, B.ru.user(rs))), 2}, z, hq)
    case False{}:
      {==}

def aff_other(n: Nat, +x: U32, +rs: List<&2, B.Ru>, +obs: List<&2, B.Ob>, +us: List<&2, B.Un>, +s: B.Ms, +z: U32, hq: {U32.is_eq(x, z) == False{} : Bool}) ->
    {B.ms.mu(s, z) == B.ms.mu(B.mult.aff(n, x, rs, obs, us, s), z) : B.Mu}:
  match n:
    case 0n:
      {==}
    case 1n+k:
      match k:
        case 0n:
          aff_k(U32.is_gt(B.mu.m(B.ms.mu(s, B.ru.user(rs))), 0), s, x, rs, z, hq)
        case 1n+p:
          ms_er(s, B.er.affine(obs, us, x, rs), z)

def of_k_other(sh: Bool, cp: Bool, +x: U32, +rs: List<&2, B.Ru>, +obs: List<&2, B.Ob>, +us: List<&2, B.Un>, +ut: B.Ht<B.Un>, +s: B.Ms, +z: U32,
    hq: {U32.is_eq(x, z) == False{} : Bool}) -> {B.ms.mu(s, z) == B.ms.mu(B.mult.of.k(sh, cp, x, rs, obs, us, ut, s), z) : B.Mu}:
  match sh cp:
    case True{} _:
      {==}
    case False{} True{}:
      ms_set_other(s, x, B.Mu{B.uses.m(rs, ut, s), 1}, z, hq)
    case False{} False{}:
      aff_other(List.length(&2, B.Ru, rs), x, rs, obs, us, s, z, hq)

# a unit's turn leaves another's disposition
def mult_of_other(+x: U32, +share: U32, +rs: List<&2, B.Ru>, +obs: List<&2, B.Ob>, +us: List<&2, B.Un>, +ut: B.Ht<B.Un>, +s: B.Ms, +z: U32,
    hq: {U32.is_eq(x, z) == False{} : Bool}) -> {B.ms.mu(s, z) == B.ms.mu(B.mult.of(x, share, rs, obs, us, ut, s), z) : B.Mu}:
  of_k_other(U32.is_eq(share, 1), U32.is_eq(share, 2), x, rs, obs, us, ut, s, z, hq)

# the turns of units other than z leave its disposition
def frozen(t: List<&2, U32>, +es: List<&2, U32>, +rss: List<&2, List<&2, B.Ru>>, +ut: B.Ht<B.Un>, +obs: List<&2, B.Ob>, +us: List<&2, B.Un>, +s: B.Ms, +z: U32,
    +hz: {B.has(t, z) == False{} : Bool}) -> {B.ms.mu(s, z) == B.ms.mu(B.mults.spec(t, es, rss, ut, obs, us, s), z) : B.Mu}:
  match t:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      Equal.trans(B.Mu, B.ms.mu(s, z), B.ms.mu(B.mult.of(x, B.mult.share(x, ut), B.uses.of(es, rss, x), obs, us, ut, s), z),
        B.ms.mu(B.mults.spec(r, es, rss, ut, obs, us, B.mult.of(x, B.mult.share(x, ut), B.uses.of(es, rss, x), obs, us, ut, s)), z),
        mult_of_other(x, B.mult.share(x, ut), B.uses.of(es, rss, x), obs, us, ut, s, z, or_false_l(U32.is_eq(x, z), B.has(r, z), hz)),
        frozen(r, es, rss, ut, obs, us, B.mult.of(x, B.mult.share(x, ut), B.uses.of(es, rss, x), obs, us, ut, s), z, or_false_r(U32.is_eq(x, z), B.has(r, z), hz)))

# a copied unit's turn
def mult_y(+y: U32, +rs: List<&2, B.Ru>, +obs: List<&2, B.Ob>, +us: List<&2, B.Un>, +ut: B.Ht<B.Un>, +s: B.Ms, hc: {B.mult.share(y, ut) == 2 : U32}) ->
    {B.ms.set(s, y, B.Mu{B.uses.m(rs, ut, s), 1}) == B.mult.of(y, B.mult.share(y, ut), rs, obs, us, ut, s) : B.Ms}:
  %Equal.sym(U32, B.mult.share(y, ut), 2, hc) : {B.ms.set(s, y, B.Mu{B.uses.m(rs, ut, s), 1}) == B.mult.of(y, _, rs, obs, us, ut, s) : B.Ms}
  {==}

def usew_eq(+u: U32, +ut: B.Ht<B.Un>, +s: B.Ms, +s2: B.Ms, h: {B.ms.mu(s, u) == B.ms.mu(s2, u) : B.Mu}) -> {B.use.w(u, ut, s) == B.use.w(u, ut, s2) : U32}:
  %h : {B.use.w(u, ut, s) == uw_k(U32.is_eq(B.un.o(B.ut.un(ut, u)), 0), B.mu.m(_)) : U32}
  {==}

# none of q in ys
def outs(q: List<&2, U32>, +ys: List<&2, U32>) -> Bool:
  match q:
    case Nil{}:
      True{}
    case Con{+u, t}:
      Bool.and(Bool.not(B.has(ys, u)), outs(t, ys))

def outs_tail(q: List<&2, U32>, +x: U32, +r: List<&2, U32>, +h: {outs(q, Con{x, r}) == True{} : Bool}) -> {outs(q, r) == True{} : Bool}:
  match q:
    case Nil{}:
      {==}
    case Con{+u, +t}:
      and_intro(Bool.not(B.has(r, u)), outs(t, r),
        not_false(B.has(r, u), or_false_r(U32.is_eq(x, u), B.has(r, u),
          not_true(B.has(Con{x, r}, u), and_l(Bool.not(B.has(Con{x, r}, u)), outs(t, Con{x, r}), h)))),
        outs_tail(t, x, r, and_r(Bool.not(B.has(Con{x, r}, u)), outs(t, Con{x, r}), h)))

# a unit none of r nor y: its disposition after y's turn and r's, as before
def fz(+u: U32, +y: U32, +r: List<&2, U32>, +es: List<&2, U32>, +rss: List<&2, List<&2, B.Ru>>, +ut: B.Ht<B.Un>, +obs: List<&2, B.Ob>, +us: List<&2, B.Un>,
    +s: B.Ms, +mu: B.Mu, +h: {B.has(Con{y, r}, u) == False{} : Bool}) -> {B.ms.mu(s, u) == B.ms.mu(B.mults.spec(r, es, rss, ut, obs, us, B.ms.set(s, y, mu)), u) : B.Mu}:
  Equal.trans(B.Mu, B.ms.mu(s, u), B.ms.mu(B.ms.set(s, y, mu), u), B.ms.mu(B.mults.spec(r, es, rss, ut, obs, us, B.ms.set(s, y, mu)), u),
    ms_set_other(s, y, mu, u, or_false_l(U32.is_eq(y, u), B.has(r, u), h)),
    frozen(r, es, rss, ut, obs, us, B.ms.set(s, y, mu), u, or_false_r(U32.is_eq(y, u), B.has(r, u), h)))

# the uses by units taken before y, weighed at y's turn and at the end
def um_frozen(q: List<&2, U32>, +rss: List<&2, List<&2, B.Ru>>, +y: U32, +r: List<&2, U32>, +es: List<&2, U32>, +ut: B.Ht<B.Un>,
    +obs: List<&2, B.Ob>, +us: List<&2, B.Un>, +s: B.Ms, +mu: B.Mu, +ho: {outs(q, Con{y, r}) == True{} : Bool}) ->
    {B.uses.m(B.uses.of(q, rss, y), ut, s) == B.uses.m(B.uses.of(q, rss, y), ut, B.mults.spec(r, es, rss, ut, obs, us, B.ms.set(s, y, mu))) : U32}:
  match q:
    case Nil{}:
      {==}
    case Con{+u, +t}:
      %uses_m_app(B.uses.in(B.rus.at(rss, u), u, y), B.uses.of(t, rss, y), ut, B.mults.spec(r, es, rss, ut, obs, us, B.ms.set(s, y, mu))) : {B.uses.m(B.uses.of(Con{u, t}, rss, y), ut, s) == _ : U32}
      %uses_m_app(B.uses.in(B.rus.at(rss, u), u, y), B.uses.of(t, rss, y), ut, s) :
        {_ == U32.add(B.uses.m(B.uses.in(B.rus.at(rss, u), u, y), ut, B.mults.spec(r, es, rss, ut, obs, us, B.ms.set(s, y, mu))), B.uses.m(B.uses.of(t, rss, y), ut, B.mults.spec(r, es, rss, ut, obs, us, B.ms.set(s, y, mu)))) : U32}
      %uses_m_in(B.rus.at(rss, u), u, y, ut, s) :
        {U32.add(_, B.uses.m(B.uses.of(t, rss, y), ut, s)) == U32.add(B.uses.m(B.uses.in(B.rus.at(rss, u), u, y), ut, B.mults.spec(r, es, rss, ut, obs, us, B.ms.set(s, y, mu))), B.uses.m(B.uses.of(t, rss, y), ut, B.mults.spec(r, es, rss, ut, obs, us, B.ms.set(s, y, mu)))) : U32}
      %uses_m_in(B.rus.at(rss, u), u, y, ut, B.mults.spec(r, es, rss, ut, obs, us, B.ms.set(s, y, mu))) :
        {U32.add(wsum(B.uses.in(B.rus.at(rss, u), u, y), B.use.w(u, ut, s)), B.uses.m(B.uses.of(t, rss, y), ut, s)) == U32.add(_, B.uses.m(B.uses.of(t, rss, y), ut, B.mults.spec(r, es, rss, ut, obs, us, B.ms.set(s, y, mu)))) : U32}
      %usew_eq(u, ut, s, B.mults.spec(r, es, rss, ut, obs, us, B.ms.set(s, y, mu)), fz(u, y, r, es, rss, ut, obs, us, s, mu,
          not_true(B.has(Con{y, r}, u), and_l(Bool.not(B.has(Con{y, r}, u)), outs(t, Con{y, r}), ho)))) :
        {U32.add(wsum(B.uses.in(B.rus.at(rss, u), u, y), B.use.w(u, ut, s)), B.uses.m(B.uses.of(t, rss, y), ut, s)) ==
          U32.add(wsum(B.uses.in(B.rus.at(rss, u), u, y), _), B.uses.m(B.uses.of(t, rss, y), ut, B.mults.spec(r, es, rss, ut, obs, us, B.ms.set(s, y, mu)))) : U32}
      %um_frozen(t, rss, y, r, es, ut, obs, us, s, mu, and_r(Bool.not(B.has(Con{y, r}, u)), outs(t, Con{y, r}), ho)) :
        {U32.add(wsum(B.uses.in(B.rus.at(rss, u), u, y), B.use.w(u, ut, s)), B.uses.m(B.uses.of(t, rss, y), ut, s)) ==
          U32.add(wsum(B.uses.in(B.rus.at(rss, u), u, y), B.use.w(u, ut, s)), _) : U32}
      {==}

# y's turn: its disposition its uses' weight, read final
def case_y(+y: U32, +r: List<&2, U32>, +q: List<&2, U32>, +rss: List<&2, List<&2, B.Ru>>, +ut: B.Ht<B.Un>, +obs: List<&2, B.Ob>, +us: List<&2, B.Un>, +s: B.Ms,
    +h1: {B.ordered(Con{y, r}, B.calls(rss)) == True{} : Bool}, +h2: {B.distinct(Con{y, r}) == True{} : Bool}, +hc: {B.mult.share(y, ut) == 2 : U32},
    +ho: {outs(q, Con{y, r}) == True{} : Bool}) ->
    {B.ms.mu(B.mults.spec(Con{y, r}, List.reverse.go(&2, U32, r, Con{y, q}), rss, ut, obs, us, s), y) ==
      B.Mu{B.uses.m(B.uses.of(List.reverse.go(&2, U32, r, Con{y, q}), rss, y), ut, B.mults.spec(Con{y, r}, List.reverse.go(&2, U32, r, Con{y, q}), rss, ut, obs, us, s)), 1} : B.Mu}:
  %Equal.sym(List<&2, B.Ru>, B.uses.of(List.reverse.go(&2, U32, r, Con{y, q}), rss, y), B.uses.of(q, rss, y), at_turn(y, r, q, rss, h1, h2)) :
    {B.ms.mu(B.mults.spec(r, List.reverse.go(&2, U32, r, Con{y, q}), rss, ut, obs, us, B.mult.of(y, B.mult.share(y, ut), _, obs, us, ut, s)), y) == B.Mu{B.uses.m(_, ut, B.mults.spec(r, List.reverse.go(&2, U32, r, Con{y, q}), rss, ut, obs, us, B.mult.of(y, B.mult.share(y, ut), _, obs, us, ut, s))), 1} : B.Mu}
  %mult_y(y, B.uses.of(q, rss, y), obs, us, ut, s, hc) : {B.ms.mu(B.mults.spec(r, List.reverse.go(&2, U32, r, Con{y, q}), rss, ut, obs, us, _), y) == B.Mu{B.uses.m(B.uses.of(q, rss, y), ut, B.mults.spec(r, List.reverse.go(&2, U32, r, Con{y, q}), rss, ut, obs, us, _)), 1} : B.Mu}
  %frozen(r, List.reverse.go(&2, U32, r, Con{y, q}), rss, ut, obs, us, B.ms.set(s, y, B.Mu{B.uses.m(B.uses.of(q, rss, y), ut, s), 1}), y, not_true(B.has(r, y), and_l(Bool.not(B.has(r, y)), B.distinct(r), h2))) :
    {_ == B.Mu{B.uses.m(B.uses.of(q, rss, y), ut, B.mults.spec(r, List.reverse.go(&2, U32, r, Con{y, q}), rss, ut, obs, us, B.ms.set(s, y, B.Mu{B.uses.m(B.uses.of(q, rss, y), ut, s), 1}))), 1} : B.Mu}
  %ms_set_self(s, y, B.Mu{B.uses.m(B.uses.of(q, rss, y), ut, s), 1}) : {_ == B.Mu{B.uses.m(B.uses.of(q, rss, y), ut, B.mults.spec(r, List.reverse.go(&2, U32, r, Con{y, q}), rss, ut, obs, us, B.ms.set(s, y, B.Mu{B.uses.m(B.uses.of(q, rss, y), ut, s), 1}))), 1} : B.Mu}
  %um_frozen(q, rss, y, r, List.reverse.go(&2, U32, r, Con{y, q}), ut, obs, us, s, B.Mu{B.uses.m(B.uses.of(q, rss, y), ut, s), 1}, ho) : {B.Mu{B.uses.m(B.uses.of(q, rss, y), ut, s), 1} == B.Mu{_, 1} : B.Mu}
  {==}

def final_k(b: Bool, +x: U32, +r: List<&2, U32>, +q: List<&2, U32>, +rss: List<&2, List<&2, B.Ru>>, +ut: B.Ht<B.Un>, +obs: List<&2, B.Ob>, +us: List<&2, B.Un>,
    +s: B.Ms, +y: U32, +eq: {b == U32.is_eq(x, y) : Bool}, +h1: {B.ordered(Con{x, r}, B.calls(rss)) == True{} : Bool}, +h2: {B.distinct(Con{x, r}) == True{} : Bool},
    +hc: {B.mult.share(y, ut) == 2 : U32}, +ho: {outs(q, Con{x, r}) == True{} : Bool},
    ih: {U32.is_eq(x, y) == False{} : Bool} -> {B.ms.mu(B.mults.spec(Con{x, r}, List.reverse.go(&2, U32, r, Con{x, q}), rss, ut, obs, us, s), y) == B.Mu{B.uses.m(B.uses.of(List.reverse.go(&2, U32, r, Con{x, q}), rss, y), ut, B.mults.spec(Con{x, r}, List.reverse.go(&2, U32, r, Con{x, q}), rss, ut, obs, us, s)), 1} : B.Mu}) -> {B.ms.mu(B.mults.spec(Con{x, r}, List.reverse.go(&2, U32, r, Con{x, q}), rss, ut, obs, us, s), y) == B.Mu{B.uses.m(B.uses.of(List.reverse.go(&2, U32, r, Con{x, q}), rss, y), ut, B.mults.spec(Con{x, r}, List.reverse.go(&2, U32, r, Con{x, q}), rss, ut, obs, us, s)), 1} : B.Mu}:
  match b:
    case True{}:
      %u32_eq_of_is_eq(x, y, Equal.sym(Bool, True{}, U32.is_eq(x, y), eq)) : {B.ms.mu(B.mults.spec(Con{x, r}, List.reverse.go(&2, U32, r, Con{x, q}), rss, ut, obs, us, s), _) == B.Mu{B.uses.m(B.uses.of(List.reverse.go(&2, U32, r, Con{x, q}), rss, _), ut, B.mults.spec(Con{x, r}, List.reverse.go(&2, U32, r, Con{x, q}), rss, ut, obs, us, s)), 1} : B.Mu}
      case_y(x, r, q, rss, ut, obs, us, s, h1, h2,
        ME.subst(U32, z => {B.mult.share(z, ut) == 2 : U32}, y, x, Equal.sym(U32, x, y, u32_eq_of_is_eq(x, y, Equal.sym(Bool, True{}, U32.is_eq(x, y), eq))), hc), ho)
    case False{}:
      ih(Equal.sym(Bool, False{}, U32.is_eq(x, y), eq))

# the order's units r, the units q taken before them: a copied unit of r
# ends weighing its uses against the dispositions at the end
def spec_final(r: List<&2, U32>, +q: List<&2, U32>, +rss: List<&2, List<&2, B.Ru>>, +ut: B.Ht<B.Un>, +obs: List<&2, B.Ob>, +us: List<&2, B.Un>, +s: B.Ms, +y: U32,
    +h1: {B.ordered(r, B.calls(rss)) == True{} : Bool}, +h2: {B.distinct(r) == True{} : Bool}, +hy: {B.has(r, y) == True{} : Bool},
    +hc: {B.mult.share(y, ut) == 2 : U32}, +ho: {outs(q, r) == True{} : Bool}) ->
    {B.ms.mu(B.mults.spec(r, List.reverse.go(&2, U32, r, q), rss, ut, obs, us, s), y) ==
      B.Mu{B.uses.m(B.uses.of(List.reverse.go(&2, U32, r, q), rss, y), ut, B.mults.spec(r, List.reverse.go(&2, U32, r, q), rss, ut, obs, us, s)), 1} : B.Mu}:
  match r:
    case Nil{}:
      Empty.absurd({B.ms.mu(B.mults.spec(Nil{}, List.reverse.go(&2, U32, Nil{}, q), rss, ut, obs, us, s), y) ==
        B.Mu{B.uses.m(B.uses.of(List.reverse.go(&2, U32, Nil{}, q), rss, y), ut, B.mults.spec(Nil{}, List.reverse.go(&2, U32, Nil{}, q), rss, ut, obs, us, s)), 1} : B.Mu},
        MB.false_ne_true()(hy))
    case Con{+x, +r2}:
      final_k(U32.is_eq(x, y), x, r2, q, rss, ut, obs, us, s, y, {==}, h1, h2, hc, ho,
        hq => spec_final(r2, Con{x, q}, rss, ut, obs, us, B.mult.of(x, B.mult.share(x, ut), B.uses.of(List.reverse.go(&2, U32, r2, Con{x, q}), rss, x), obs, us, ut, s), y,
          and_r(B.all.in(B.ids.at(B.calls(rss), x), r2), B.ordered(r2, B.calls(rss)), h1), and_r(Bool.not(B.has(r2, x)), B.distinct(r2), h2),
          or_drop(U32.is_eq(x, y), B.has(r2, y), hq, hy), hc,
          and_intro(Bool.not(B.has(r2, x)), outs(q, r2), and_l(Bool.not(B.has(r2, x)), B.distinct(r2), h2), outs_tail(q, x, r2, ho))))

def Laws.sharing.final(xs, rss, ut, obs, us, s, y, h1, h2, hy, hc):
  spec_final(xs, Nil{}, rss, ut, obs, us, s, y, h1, h2, hy, hc, {==})

# The copied units' copies
# ------------------------
#
# The two halves joined: the writer's counter rises by the uses' weight
# (`sharing.counts`), which is the copied unit's disposition at the end
# (`sharing.final`), mults's the specification's (`mults.uses`).

def ms_mu_ms(s: B.Ms, +y: U32) -> {B.ms.mu(s, y) == B.ms.mu(B.Ms{B.ms.ms(s), Nil{}}, y) : B.Mu}:
  match s:
    case B.Ms{ms, ers}:
      {==}

# the uses' weight reads only the dispositions' table
def um_ms(rs: List<&2, B.Ru>, +ut: B.Ht<B.Un>, +s: B.Ms) -> {B.uses.m(rs, ut, s) == B.uses.m(rs, ut, B.Ms{B.ms.ms(s), Nil{}}) : U32}:
  match rs:
    case Nil{}:
      {==}
    case Con{r, +t}:
      match r:
        case B.Ru{+u, +no}:
          %usew_eq(u, ut, s, B.Ms{B.ms.ms(s), Nil{}}, ms_mu_ms(s, u)) :
            {U32.add(B.use.w(u, ut, s), B.uses.m(t, ut, s)) == U32.add(_, B.uses.m(t, ut, B.Ms{B.ms.ms(s), Nil{}})) : U32}
          %um_ms(t, ut, s) : {U32.add(B.use.w(u, ut, s), B.uses.m(t, ut, s)) == U32.add(B.use.w(u, ut, s), _) : U32}
          {==}

# y's disposition as the writer reads it
def mu_y(+xs: List<&2, U32>, +rss: List<&2, List<&2, B.Ru>>, +ut: B.Ht<B.Un>, +obs: List<&2, B.Ob>, +us: List<&2, B.Un>, +s: B.Ms, +e: B.Ec, +y: U32,
    +h1: {B.ordered(xs, B.calls(rss)) == True{} : Bool}, +h2: {B.distinct(xs) == True{} : Bool}, +hy: {B.has(xs, y) == True{} : Bool},
    +hc: {B.mult.share(y, ut) == 2 : U32}, +hms: {B.ec.ms(e) == B.Ms{B.ms.ms(B.mults(xs, B.pw.of(List<&2, B.Ru>, rss), ut, obs, us, s, {B.WmNone{} : B.Wm<List<&2, B.Ru>>})), Nil{}} : B.Ms}) ->
    {B.ec.mu(e, y) == B.Mu{B.uses.m(B.uses.of(List.reverse(&2, U32, xs), rss, y), ut, B.mults.spec(xs, List.reverse(&2, U32, xs), rss, ut, obs, us, s)), 1} : B.Mu}:
  %Equal.sym(B.Mu, B.ec.mu(e, y), B.ms.mu(B.ec.ms(e), y), mu_e(e, y)) : {_ == B.Mu{B.uses.m(B.uses.of(List.reverse(&2, U32, xs), rss, y), ut, B.mults.spec(xs, List.reverse(&2, U32, xs), rss, ut, obs, us, s)), 1} : B.Mu}
  %Equal.sym(B.Ms, B.ec.ms(e), B.Ms{B.ms.ms(B.mults(xs, B.pw.of(List<&2, B.Ru>, rss), ut, obs, us, s, {B.WmNone{} : B.Wm<List<&2, B.Ru>>})), Nil{}}, hms) : {B.ms.mu(_, y) == B.Mu{B.uses.m(B.uses.of(List.reverse(&2, U32, xs), rss, y), ut, B.mults.spec(xs, List.reverse(&2, U32, xs), rss, ut, obs, us, s)), 1} : B.Mu}
  %ms_mu_ms(B.mults(xs, B.pw.of(List<&2, B.Ru>, rss), ut, obs, us, s, {B.WmNone{} : B.Wm<List<&2, B.Ru>>}), y) : {_ == B.Mu{B.uses.m(B.uses.of(List.reverse(&2, U32, xs), rss, y), ut, B.mults.spec(xs, List.reverse(&2, U32, xs), rss, ut, obs, us, s)), 1} : B.Mu}
  %Equal.sym(B.Ms, B.mults(xs, B.pw.of(List<&2, B.Ru>, rss), ut, obs, us, s, {B.WmNone{} : B.Wm<List<&2, B.Ru>>}), B.mults.spec(xs, List.reverse(&2, U32, xs), rss, ut, obs, us, s), Laws.mults.uses(xs, rss, ut, obs, us, s, h1, h2)) : {B.ms.mu(_, y) == B.Mu{B.uses.m(B.uses.of(List.reverse(&2, U32, xs), rss, y), ut, B.mults.spec(xs, List.reverse(&2, U32, xs), rss, ut, obs, us, s)), 1} : B.Mu}
  Laws.sharing.final(xs, rss, ut, obs, us, s, y, h1, h2, hy, hc)

def kind_y(+e: B.Ec, +y: U32, +u: U32, h: {B.ec.mu(e, y) == B.Mu{u, 1} : B.Mu}) -> {B.mu.kind(B.ec.mu(e, y)) == 1 : U32}:
  %Equal.sym(B.Mu, B.ec.mu(e, y), B.Mu{u, 1}, h) : {B.mu.kind(_) == 1 : U32}
  {==}

def Laws.sharing.copied(xs, rss, ut, obs, us, s, e, acc, y, h1, h2, hy, hc, hm, hut, hms, hu):
  %Equal.sym(B.Mu, B.ec.mu(e, y), B.Mu{B.uses.m(B.uses.of(List.reverse(&2, U32, xs), rss, y), ut, B.mults.spec(xs, List.reverse(&2, U32, xs), rss, ut, obs, us, s)), 1}, mu_y(xs, rss, ut, obs, us, s, e, y, h1, h2, hy, hc, hms)) : {B.ctr.at(B.tb.ctrs(B.order.put(List.reverse(&2, U32, xs), e, B.Tb{acc, B.WmNone{}})), y) == U32.add(1, B.mu.m(_)) : U32}
  %Equal.sym(U32, B.uses.m(B.uses.of(List.reverse(&2, U32, xs), rss, y), ut, B.mults.spec(xs, List.reverse(&2, U32, xs), rss, ut, obs, us, s)), B.uses.m(B.uses.of(List.reverse(&2, U32, xs), rss, y), ut, B.Ms{B.ms.ms(B.mults.spec(xs, List.reverse(&2, U32, xs), rss, ut, obs, us, s)), Nil{}}), um_ms(B.uses.of(List.reverse(&2, U32, xs), rss, y), ut, B.mults.spec(xs, List.reverse(&2, U32, xs), rss, ut, obs, us, s))) : {B.ctr.at(B.tb.ctrs(B.order.put(List.reverse(&2, U32, xs), e, B.Tb{acc, B.WmNone{}})), y) == U32.add(1, _) : U32}
  %Laws.mults.uses(xs, rss, ut, obs, us, s, h1, h2) : {B.ctr.at(B.tb.ctrs(B.order.put(List.reverse(&2, U32, xs), e, B.Tb{acc, B.WmNone{}})), y) == U32.add(1, B.uses.m(B.uses.of(List.reverse(&2, U32, xs), rss, y), ut, B.Ms{B.ms.ms(_), Nil{}})) : U32}
  %hms : {B.ctr.at(B.tb.ctrs(B.order.put(List.reverse(&2, U32, xs), e, B.Tb{acc, B.WmNone{}})), y) == U32.add(1, B.uses.m(B.uses.of(List.reverse(&2, U32, xs), rss, y), ut, _)) : U32}
  %hut : {B.ctr.at(B.tb.ctrs(B.order.put(List.reverse(&2, U32, xs), e, B.Tb{acc, B.WmNone{}})), y) == U32.add(1, B.uses.m(B.uses.of(List.reverse(&2, U32, xs), rss, y), _, B.ec.ms(e))) : U32}
  %hu : {B.ctr.at(B.tb.ctrs(B.order.put(List.reverse(&2, U32, xs), e, B.Tb{acc, B.WmNone{}})), y) == U32.add(1, B.uses.m(_, B.ec.ut(e), B.ec.ms(e))) : U32}
  %um_get_none(U32, y) : {B.ctr.at(B.tb.ctrs(B.order.put(List.reverse(&2, U32, xs), e, B.Tb{acc, B.WmNone{}})), y) == U32.add(B.ctr.or(_), B.uses.m(B.uses.of.e(List.reverse(&2, U32, xs), e, y), B.ec.ut(e), B.ec.ms(e))) : U32}
  Laws.sharing.counts(List.reverse(&2, U32, xs), e, B.Tb{acc, B.WmNone{}}, y, hm,
    kind_y(e, y, B.uses.m(B.uses.of(List.reverse(&2, U32, xs), rss, y), ut, B.mults.spec(xs, List.reverse(&2, U32, xs), rss, ut, obs, us, s)), mu_y(xs, rss, ut, obs, us, s, e, y, h1, h2, hy, hc, hms)))
