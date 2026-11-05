# Blend's own laws (docs/plans/Blend_2026-11-04.md, `blend-laws`), the
# guarantees a user sees first. PROOF.bend proves them.

import Base
import ./blend.bend as B

# LAW: `same` says two names are the same only where they are equal, so a
# reference binds to the definition it names and no other.
# Record: blend-namespaces-as-bends
law names.same_eq:
  for +a: List<&2, U32>
  for +b: List<&2, U32>
  for +h: {B.same(a, b) == True{} : Bool}
  {a == b : List<&2, U32>}

# LAW: and every name is the same as itself.
# Record: blend-namespaces-as-bends
law names.same_refl:
  for +a: List<&2, U32>
  {B.same(a, a) == True{} : Bool}

# LAW: a dotted name split into its parts and joined back is itself, so a
# path names what its writer wrote (`Outer.Inner.f`).
# Record: blend-namespaces-as-bends
law names.dots_parts:
  for +x: List<&2, U32>
  {B.dots(B.parts(x)) == x : List<&2, U32>}

# LAW: a token that names nothing, a number, a string, a comment, a space,
# a symbol or an empty name, is emitted as it is written: a body is Bend,
# its references aside.
# Record: blend-adds-no-bend-logic
law locals.not_name:
  for +cx: B.Cx
  for +o: U32
  for +q: U32
  for +locals: List<&2, List<&2, U32>>
  for +t: B.Tok
  for +no: U32
  for h: {B.tok.txt(t) == Nil{} : List<&2, U32>}
  {B.rr.of(cx, o, q, locals, t, no) == B.rr.tok(t) : B.Rr}

# LAW: a name a local binds, a parameter or a binding of the body, is
# emitted as it is written, bound to no definition; a name beginning `^`
# (a host's) or `~` (a template's argument) aside.
# Record: blend-no-shadowing
law locals.kept:
  for +cx: B.Cx
  for +o: U32
  for +q: U32
  for +locals: List<&2, List<&2, U32>>
  for +h: U32
  for +r: List<&2, U32>
  for +no: U32
  for a: {U32.is_eq(h, 94) == False{} : Bool}
  for b: {U32.is_eq(h, 126) == False{} : Bool}
  for +l: {B.names.has(locals, Con{h, r}) == True{} : Bool}
  {B.rr.of(cx, o, q, locals, B.TName{Con{h, r}}, no) == B.rr.tok(B.TName{Con{h, r}}) : B.Rr}

# LAW: and a local passed on as a template's argument, `~f`, likewise.
# Record: blend-no-shadowing
law locals.template:
  for +cx: B.Cx
  for +o: U32
  for +q: U32
  for +locals: List<&2, List<&2, U32>>
  for +r: List<&2, U32>
  for +no: U32
  for l: {B.names.has(locals, r) == True{} : Bool}
  {B.rr.of(cx, o, q, locals, B.TName{Con{126, r}}, no) == B.rr.tok(B.TName{Con{126, r}}) : B.Rr}

# LAW: a line's tokens spell it exactly, every byte in a token, in order,
# none dropped and none added: a body is emitted as written, its
# references aside.
# Record: blend-adds-no-bend-logic
law tokens.spell:
  for +xs: List<&2, U32>
  {B.toks.text(B.toks(xs)) == xs : List<&2, U32>}

# LAW: a file's lines, each its indentation's spaces then its text,
# joined back by newlines, are the file's bytes less carriage returns:
# Blend reads every byte of a file but those. For a file shorter than
# 2^32 bytes, as every file Blend reads is (its size a U32).
# Record: blend-adds-no-bend-logic
law lines.join:
  for +bs: List<&2, U32>
  for h: {Nat.is_lt(List.length(&2, U32, bs), Nat.pow(2n, 32n)) == True{} : Bool}
  {B.lines.text(B.lines(bs)) == B.uncr(bs) : List<&2, U32>}

# LAW: the walk's order, emitted reversed, puts each unit after the units
# it calls, as Bend requires a definition after those it calls; whatever
# the roots and the calls, a cycle among them reported, never emitted.
# Record: blend-adds-no-bend-logic
law order.callees_first:
  for +roots: List<&2, U32>
  for +cal: List<&2, List<&2, U32>>
  for +obs: List<&2, B.Ob>
  for +us: List<&2, B.Un>
  {B.ordered(B.ds.order(B.walk(roots, cal, obs, us)), cal) == True{} : Bool}

# LAW: the walk's order holds each unit once at most: with
# order.callees_first, each definition is emitted after its callees and
# none twice.
# Record: blend-adds-no-bend-logic
law order.once:
  for +roots: List<&2, U32>
  for +cal: List<&2, List<&2, U32>>
  for +obs: List<&2, B.Ob>
  for +us: List<&2, B.Un>
  {B.distinct(B.ds.order(B.walk(roots, cal, obs, us))) == True{} : Bool}

# LAW: where the walk reports no error, every unit it walked is in its
# order: the order's guard (a unit joins once its callees have) held none
# back, and nothing walked is lost.
# Record: blend-adds-no-bend-logic
law order.walked:
  for +roots: List<&2, U32>
  for +cal: List<&2, List<&2, U32>>
  for +obs: List<&2, B.Ob>
  for +us: List<&2, B.Un>
  for h: {List.is_empty(&2, B.Er, B.ds.ers(B.walk(roots, cal, obs, us))) == True{} : Bool}
  {B.all.in(B.ds.walked(B.walk(roots, cal, obs, us)), B.ds.order(B.walk(roots, cal, obs, us))) == True{} : Bool}

# LAW: once the walk has finished, its stack and its roots spent, every
# root has been walked.
# Record: blend-adds-no-bend-logic
law order.roots:
  for +roots: List<&2, U32>
  for +cal: List<&2, List<&2, U32>>
  for +obs: List<&2, B.Ob>
  for +us: List<&2, B.Un>
  for h: {B.ds.finished(B.walk(roots, cal, obs, us)) == True{} : Bool}
  {B.all.in(roots, B.ds.walked(B.walk(roots, cal, obs, us))) == True{} : Bool}

# LAW: once the walk has finished, every unit a walked unit calls has been
# walked: with order.roots, every unit a root reaches, so that nothing a
# definition calls is left out.
# Record: blend-adds-no-bend-logic
law order.closed:
  for +roots: List<&2, U32>
  for +cal: List<&2, List<&2, U32>>
  for +obs: List<&2, B.Ob>
  for +us: List<&2, B.Un>
  for h: {B.ds.finished(B.walk(roots, cal, obs, us)) == True{} : Bool}
  {B.calls.in(B.ds.walked(B.walk(roots, cal, obs, us)), cal, B.ds.walked(B.walk(roots, cal, obs, us))) == True{} : Bool}

# LAW: the walk finishes within its fuel, whatever its roots and calls,
# so that `order.roots` and `order.closed` hold always: every root and
# every unit one reaches is walked, each in its order once
# (`order.once`), after its callees (`order.callees_first`), and in it
# where no error is reported (`order.walked`).
# Record: blend-adds-no-bend-logic
law order.ends:
  for +roots: List<&2, U32>
  for +cal: List<&2, List<&2, U32>>
  for +obs: List<&2, B.Ob>
  for +us: List<&2, B.Un>
  {B.ds.finished(B.walk(roots, cal, obs, us)) == True{} : Bool}

# LAW: the walk the tool runs is the walk the laws above follow: with
# its sets dropped, its state is walk's, so that each of those laws holds
# of the order Blend emits (`blend-scale.walk`).
# Record: blend-adds-no-bend-logic
law order.fast:
  for +roots: List<&2, U32>
  for +cal: List<&2, List<&2, U32>>
  for +obs: List<&2, B.Ob>
  for +us: List<&2, B.Un>
  {B.df.ds(B.walk.fast(roots, cal, obs, us)) == B.walk(roots, cal, obs, us) : B.Ds}

# LAW: the writer writes each unit of an order by its own name, then
# once for each copy its sharing asks for, and nothing else, in order:
# with the order's laws, each definition once, after its callees.
# Record: blend-copies-keep-their-name
law emit.defs:
  for xs: List<&2, U32>
  for +e: B.Ec
  for +b: B.Tb
  {B.order.put(xs, e, b) == B.defs.put(B.defs.of(xs, e), e, b) : B.Tb}

# LAW: and the names the check of names emitted twice examines are the
# names of those definitions, so that it checks what is written.
# Record: blend-copies-keep-their-name
law emit.names:
  for xs: List<&2, U32>
  for +e: B.Ec
  {B.names.all(xs, e) == B.defs.names(B.defs.of(xs, e), e) : List<&2, B.Nm>}

# LAW: and where that check reports none, the names of the definitions
# written are distinct, so that each is Bend's by a name of its own.
# Record: blend-namespaces-as-bends, blend-copies-keep-their-name
law emit.unique:
  for +xs: List<&2, U32>
  for +e: B.Ec
  for +h: {B.er.names.of(B.names.all(xs, e)) == Nil{} : List<&2, B.Er>}
  {B.nms.distinct(B.defs.names(B.defs.of(xs, e), e)) == True{} : Bool}

# LAW: mults, which hands each unit's uses on to the units it uses as it
# goes, gives each unit the copies its uses by all the units emitted ask
# for, as a search of them gathers them (mults.spec), where the order is
# callee-first and holds each unit once, as the walk's is
# (`order.callees_first`, `order.once`).
# Record: blend-copies-keep-their-name
law mults.uses:
  for xs: List<&2, U32>
  for +rss: List<&2, List<&2, B.Ru>>
  for +ut: B.Ht<B.Un>
  for +obs: List<&2, B.Ob>
  for +us: List<&2, B.Un>
  for s: B.Ms
  for +h1: {B.ordered(xs, B.calls(rss)) == True{} : Bool}
  for +h2: {B.distinct(xs) == True{} : Bool}
  {B.mults(xs, B.pw.of(List<&2, B.Ru>, rss), ut, obs, us, s, {B.WmNone{} : B.Wm<List<&2, B.Ru>>}) ==
    B.mults.spec(xs, List.reverse(&2, U32, xs), rss, ut, obs, us, s) : B.Ms}

# LAW: so for the order Blend walks: each unit's copies are those its uses
# by all the units emitted ask for.
# Record: blend-copies-keep-their-name
law mults.walked:
  for +roots: List<&2, U32>
  for +rss: List<&2, List<&2, B.Ru>>
  for +ut: B.Ht<B.Un>
  for +obs: List<&2, B.Ob>
  for +us: List<&2, B.Un>
  for s: B.Ms
  {B.mults(B.ds.order(B.df.ds(B.walk.fast(roots, B.calls(rss), obs, us))), B.pw.of(List<&2, B.Ru>, rss), ut, obs, us, s, {B.WmNone{} : B.Wm<List<&2, B.Ru>>}) ==
    B.mults.spec(B.ds.order(B.df.ds(B.walk.fast(roots, B.calls(rss), obs, us))), List.reverse(&2, U32, B.ds.order(B.df.ds(B.walk.fast(roots, B.calls(rss), obs, us)))),
      rss, ut, obs, us, s) : B.Ms}

# LAW: a merge that succeeds keeps every list it merges as a subsequence
# and holds each object once: an object's linearization keeps each of its
# parents' linearizations, and its list of parents, in their order.
# Record: blend-c3
law c3.sound:
  for +n: Nat
  for +seqs: List<&2, B.Sq>
  {B.mg.sound(B.c3.merge(n, seqs, Nil{}), seqs) == True{} : Bool}

# LAW: and an object's linearization fails only where no order holding
# each object once keeps every list it merges, its parents'
# linearizations and its list of parents: given one, the merge succeeds,
# within its fuel.
# Record: blend-c3
law c3.complete:
  for +id: U32
  for +ps: List<&2, U32>
  for +seqs: List<&2, B.Sq>
  for +ys: List<&2, U32>
  for +h1: {B.sqs.kept(List.append(&2, B.Sq, seqs, [B.Sq{id, ps}]), ys) == True{} : Bool}
  for +h2: {B.distinct(ys) == True{} : Bool}
  {B.lz.ok(B.lin.of(id, ps, Some{seqs})) == True{} : Bool}

# LAW: a linearization begins with its object, merged or not.
# Record: blend-c3
law c3.first:
  for +id: U32
  for +ps: List<&2, U32>
  for ss: Maybe<&2, List<&2, B.Sq>>
  {List.head(&2, U32, B.lz.ord(Some{B.lin.of(id, ps, ss)})) == Some{id} : Maybe<&2, U32>}

# LAW: writing an order into the code's file, each copied unit's counter
# of numbered calls rises by what its uses by the units written ask: at
# each use, one for each of the user's copies, none from a module's
# definition, as the dispositions weigh uses (`uses.m`), the uses those
# the writer reads.
# Record: blend-copies-keep-their-name
law sharing.counts:
  for +xs: List<&2, U32>
  for +e: B.Ec
  for +b: B.Tb
  for +y: U32
  for +hm: {B.ec.mode(e) == 0 : U32}
  for +hk: {B.mu.kind(B.ec.mu(e, y)) == 1 : U32}
  {B.ctr.at(B.tb.ctrs(B.order.put(xs, e, b)), y) == U32.add(B.ctr.at(B.tb.ctrs(b), y), B.uses.m(B.uses.of.e(xs, e, y), B.ec.ut(e), B.ec.ms(e))) : U32}

# LAW: in an order callee-first and holding each unit once, as the walk's
# is, a copied unit's disposition at the end weighs its uses against the
# dispositions at the end: its users' are final at its turn.
# Record: blend-copies-keep-their-name
law sharing.final:
  for +xs: List<&2, U32>
  for +rss: List<&2, List<&2, B.Ru>>
  for +ut: B.Ht<B.Un>
  for +obs: List<&2, B.Ob>
  for +us: List<&2, B.Un>
  for +s: B.Ms
  for +y: U32
  for +h1: {B.ordered(xs, B.calls(rss)) == True{} : Bool}
  for +h2: {B.distinct(xs) == True{} : Bool}
  for +hy: {B.has(xs, y) == True{} : Bool}
  for +hc: {B.mult.share(y, ut) == 2 : U32}
  {B.ms.mu(B.mults.spec(xs, List.reverse(&2, U32, xs), rss, ut, obs, us, s), y) ==
    B.Mu{B.uses.m(B.uses.of(List.reverse(&2, U32, xs), rss, y), ut, B.mults.spec(xs, List.reverse(&2, U32, xs), rss, ut, obs, us, s)), 1} : B.Mu}

# LAW: so, writing the walk's order into the code's file with the
# dispositions mults makes, each copied unit's counter ends at one more
# than its numbered copies: the writer numbers calls from 1 up, one at a
# time, so that each numbered copy has one caller, its number its own.
# Given that the writer reads the uses mults reads (both from the units'
# list: emission's table holds it, unproved).
# Record: blend-copies-keep-their-name
law sharing.copied:
  for +xs: List<&2, U32>
  for +rss: List<&2, List<&2, B.Ru>>
  for +ut: B.Ht<B.Un>
  for +obs: List<&2, B.Ob>
  for +us: List<&2, B.Un>
  for +s: B.Ms
  for +e: B.Ec
  for +acc: List<&2, U32>
  for +y: U32
  for +h1: {B.ordered(xs, B.calls(rss)) == True{} : Bool}
  for +h2: {B.distinct(xs) == True{} : Bool}
  for +hy: {B.has(xs, y) == True{} : Bool}
  for +hc: {B.mult.share(y, ut) == 2 : U32}
  for +hm: {B.ec.mode(e) == 0 : U32}
  for +hut: {B.ec.ut(e) == ut : B.Ht<B.Un>}
  for +hms: {B.ec.ms(e) == B.Ms{B.ms.ms(B.mults(xs, B.pw.of(List<&2, B.Ru>, rss), ut, obs, us, s, {B.WmNone{} : B.Wm<List<&2, B.Ru>>})), Nil{}} : B.Ms}
  for +hu: {B.uses.of.e(List.reverse(&2, U32, xs), e, y) == B.uses.of(List.reverse(&2, U32, xs), rss, y) : List<&2, B.Ru>}
  {B.ctr.at(B.tb.ctrs(B.order.put(List.reverse(&2, U32, xs), e, B.Tb{acc, B.WmNone{}})), y) == U32.add(1, B.mu.m(B.ec.mu(e, y))) : U32}
