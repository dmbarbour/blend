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
  for +no: B.Loc
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
  for +no: B.Loc
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
  for +no: B.Loc
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
  for +ut: B.Ht<B.Pk<B.Un>>
  for +obs: List<&2, B.Ob>
  for +us: List<&2, B.Un>
  for s: B.Ms
  for +h1: {B.ordered(xs, B.calls(rss)) == True{} : Bool}
  for +h2: {B.distinct(xs) == True{} : Bool}
  {B.mults(xs, B.pw.of(List<&2, B.Ru>, rss), ut, obs, us, s, {B.HLeaf{Nil{}} : B.Ht<B.Pk<List<&2, B.Ru>>>}) ==
    B.mults.spec(xs, List.reverse(&2, U32, xs), rss, ut, obs, us, s) : B.Ms}

# LAW: so for the order Blend walks: each unit's copies are those its uses
# by all the units emitted ask for.
# Record: blend-copies-keep-their-name
law mults.walked:
  for +roots: List<&2, U32>
  for +rss: List<&2, List<&2, B.Ru>>
  for +ut: B.Ht<B.Pk<B.Un>>
  for +obs: List<&2, B.Ob>
  for +us: List<&2, B.Un>
  for s: B.Ms
  {B.mults(B.ds.order(B.df.ds(B.walk.fast(roots, B.calls(rss), obs, us))), B.pw.of(List<&2, B.Ru>, rss), ut, obs, us, s, {B.HLeaf{Nil{}} : B.Ht<B.Pk<List<&2, B.Ru>>>}) ==
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

# LAW: and where an object's linearization succeeds, it is the object,
# then an order holding each object once that keeps each of its parents'
# linearizations and its list of parents, in their order: `lin.of`
# merges what C3 says (`c3.sound` over those lists).
# Record: blend-c3
law c3.lin:
  for +id: U32
  for +ps: List<&2, U32>
  for +seqs: List<&2, B.Sq>
  {B.lz.sound(B.lin.of(id, ps, Some{seqs}), id, List.append(&2, B.Sq, seqs, [B.Sq{id, ps}])) == True{} : Bool}

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
  for +ut: B.Ht<B.Pk<B.Un>>
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
  for +ut: B.Ht<B.Pk<B.Un>>
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
  for +hut: {B.ec.ut(e) == ut : B.Ht<B.Pk<B.Un>>}
  for +hms: {B.ec.ms(e) == B.Ms{B.ms.ms(B.mults(xs, B.pw.of(List<&2, B.Ru>, rss), ut, obs, us, s, {B.HLeaf{Nil{}} : B.Ht<B.Pk<List<&2, B.Ru>>>})), Nil{}} : B.Ms}
  for +hu: {B.uses.of.e(List.reverse(&2, U32, xs), e, y) == B.uses.of(List.reverse(&2, U32, xs), rss, y) : List<&2, B.Ru>}
  {B.ctr.at(B.tb.ctrs(B.order.put(List.reverse(&2, U32, xs), e, B.Tb{acc, B.HLeaf{Nil{}}})), y) == U32.add(1, B.mu.m(B.ec.mu(e, y))) : U32}

# LAW: where the dispositions report no error, each affine unit of the
# order has one use at most: a second is an error, and an error stays.
# Record: blend-templates-affine
law sharing.once:
  for +xs: List<&2, U32>
  for +rss: List<&2, List<&2, B.Ru>>
  for +ut: B.Ht<B.Pk<B.Un>>
  for +obs: List<&2, B.Ob>
  for +us: List<&2, B.Un>
  for +s: B.Ms
  for +y: U32
  for +hy: {B.has(xs, y) == True{} : Bool}
  for +ha: {B.mult.share(y, ut) == 0 : U32}
  for +he: {B.ms.ers(B.mults.spec(xs, List.reverse(&2, U32, xs), rss, ut, obs, us, s)) == Nil{} : List<&2, B.Er>}
  {Nat.is_le(List.length(&2, B.Ru, B.uses.of(List.reverse(&2, U32, xs), rss, y)), 1n) == True{} : Bool}

# LAW: and an affine unit used once ends with its one user's copies, of
# the affine kind where there are any, so that the writer, calling its
# copy of each of the user's numbers from the user's copy of that number
# (`ref.kind.k`), gives each copy one caller; with none, it stays as it
# was, its one caller the user's one copy.
# Record: blend-copies-keep-their-name
law sharing.affine:
  for +xs: List<&2, U32>
  for +rss: List<&2, List<&2, B.Ru>>
  for +ut: B.Ht<B.Pk<B.Un>>
  for +obs: List<&2, B.Ob>
  for +us: List<&2, B.Un>
  for +s: B.Ms
  for +y: U32
  for +h1: {B.ordered(xs, B.calls(rss)) == True{} : Bool}
  for +h2: {B.distinct(xs) == True{} : Bool}
  for +hy: {B.has(xs, y) == True{} : Bool}
  for +ha: {B.mult.share(y, ut) == 0 : U32}
  for +hl: {List.length(&2, B.Ru, B.uses.of(List.reverse(&2, U32, xs), rss, y)) == 1n : Nat}
  {B.ms.mu(B.mults.spec(xs, List.reverse(&2, U32, xs), rss, ut, obs, us, s), y) ==
    B.mu.after(B.mu.m(B.ms.mu(B.mults.spec(xs, List.reverse(&2, U32, xs), rss, ut, obs, us, s), B.ru.user(B.uses.of(List.reverse(&2, U32, xs), rss, y)))),
      B.ms.mu(s, y)) : B.Mu}

# LAW: a file's lines are numbered from its base, one more each, none
# skipped: the line a marker names and those after it are the file's.
# Record: blend-adds-no-bend-logic
law markers.lines:
  for +bs: List<&2, U32>
  for +base: B.Loc
  {B.ln.from(B.lines.at(bs, base), B.loc.next(base)) == True{} : Bool}

# LAW: lines numbered one more each read as items, each definition's body
# is the lines after its header's, none dropped nor merged, numbered on
# from its header's line (a type member's from that line itself), and a
# datatype's lines from its own: what a marker counts on.
# Record: blend-adds-no-bend-logic
law markers.items:
  for +ls: List<&2, B.Ln>
  for +k: B.Loc
  for +h: {B.ln.from(ls, k) == True{} : Bool}
  {B.items.ok(B.flat(ls)) == True{} : Bool}

# LAW: and any lines read as items, every definition's body is clear of
# a marker's place: each line blank or deeper than its header, but a
# type member's one line, numbered as its header (`ln.deep`), so that
# the writer writes none at a line's start (`markers.unambiguous`).
# Record: blend-adds-no-bend-logic
law deep.items:
  for +ls: List<&2, B.Ln>
  {B.items.deep(B.flat(ls)) == True{} : Bool}

# LAW: lines numbered one more each, within a line, read as items: every
# datatype's lines are numbered on from its line, the first its `type`
# header, the rest blank or deeper than it, each within a line
# (`bend.ok`), as `markers.datatypes` takes them.
# Record: blend-adds-no-bend-logic
law bends.items:
  for +ls: List<&2, B.Ln>
  for +k: B.Loc
  for +h: {B.ln.from(ls, k) == True{} : Bool}
  for +hi: {B.lns.inline(ls) == True{} : Bool}
  {B.items.bend(B.flat(ls)) == True{} : Bool}

# LAW: and items so make a tree whose datatypes keep their lines so
# (`nodes.bend`).
# Record: blend-adds-no-bend-logic
law bends.tree:
  for +its: List<&2, B.Item>
  for +h: {B.items.bend(its) == True{} : Bool}
  {B.nodes.bend(B.tree(its)) == True{} : Bool}

# LAW: so a file read: every datatype's lines as `markers.datatypes`
# takes them.
# Record: blend-adds-no-bend-logic
law bends.read:
  for +bs: List<&2, U32>
  for +base: B.Loc
  {B.nodes.bend(B.read.at(bs, base)) == True{} : Bool}

# LAW: and every object's members, the made objects' included, keep the
# datatypes of the trees they come from so.
# Record: blend-adds-no-bend-logic
law bends.members:
  for +trees: List<&2, List<&2, B.Node>>
  for +als: List<&2, B.Al>
  for +h: {B.trees.bend(trees) == True{} : Bool}
  {B.obs.mems.bend(B.obs.made(B.syn.of(als, B.obs(trees)))) == True{} : Bool}

# LAW: so the datatypes the code's file is written with, the root's
# members, are written as where.sh reads them (`markers.datatypes`), the
# hypotheses the reader's alone: the files' names (`inline.files`) and the
# trees as read (`bends.read`).
# Record: blend-adds-no-bend-logic
law datatypes.emitted:
  for +files: List<&2, List<&2, U32>>
  for +trees: List<&2, List<&2, B.Node>>
  for +als: List<&2, B.Al>
  for +hf: {B.inlines(files) == True{} : Bool}
  for +hb: {B.trees.bend(trees) == True{} : Bool}
  {B.dts.where(B.ob.mems(B.ob.at(B.obs.made(B.syn.of(als, B.obs(trees))), 0)), files) == True{} : Bool}

# LAW: and items so make a tree whose definitions keep their bodies so,
# each line's depth and blankness kept (`bl.deep`).
# Record: blend-adds-no-bend-logic
law deep.tree:
  for +its: List<&2, B.Item>
  for +h: {B.items.deep(its) == True{} : Bool}
  {B.defs.deep(B.tree(its)) == True{} : Bool}

# LAW: so a file read: every definition's body clear of a marker's place.
# Record: blend-adds-no-bend-logic
law deep.read:
  for +bs: List<&2, U32>
  for +base: B.Loc
  {B.defs.deep(B.read.at(bs, base)) == True{} : Bool}

# LAW: and the units copied from trees so, each where its definition is
# found, have lines so: its body's, line for line at the same depth, a
# blank one blank, whatever object holds it (`rl.deep`), as
# `markers.writer` and `markers.unambiguous` take them.
# Record: blend-adds-no-bend-logic
law deep.units:
  for +trees: List<&2, List<&2, B.Node>>
  for +als: List<&2, B.Al>
  for +ls: List<&2, Maybe<&2, B.Lz>>
  for +fs: List<&2, Maybe<&2, B.Fd>>
  for +als2: List<&2, B.Al>
  for +paths: List<&2, List<&2, U32>>
  for +pss: List<&2, List<&2, U32>>
  for +h: {B.trees.deep(trees) == True{} : Bool}
  {B.units.deep(B.units(B.module.copies(B.obs.made(B.syn.of(als, B.obs(trees))),
    B.cx.of(B.obs.made(B.syn.of(als, B.obs(trees))), ls, fs, als2, paths, pss)))) == True{} : Bool}

# LAW: each unit a module's objects copy has, where its definition is
# found, one its objects' members hold: the member table finds among
# them, and the copies make none. With `nodes.objects`, every unit's
# definition is one a module's tree holds.
# Record: blend-adds-no-bend-logic
law nodes.copies:
  for +obs: List<&2, B.Ob>
  for +ls: List<&2, Maybe<&2, B.Lz>>
  for +fs: List<&2, Maybe<&2, B.Fd>>
  for +als: List<&2, B.Al>
  for +paths: List<&2, List<&2, U32>>
  for +pss: List<&2, List<&2, U32>>
  for +ds: List<&2, B.Node>
  for +h: {B.objs.within(obs, ds) == True{} : Bool}
  {B.units.held(B.units(B.module.copies(obs, B.cx.of(obs, ls, fs, als, paths, pss))), ds) == True{} : Bool}

# LAW: an object's copies leave none of its finals uncopied, whatever
# module defines them, where they report no error: each instance the
# copies' worklist takes ends in its set of instances done, copied there
# or found there, and a worklist past its fuel reports an error rather
# than drop the rest silently, as one did while its fuel was the root
# file's definitions (`blend-scale.copies-fuel`).
# Record: blend-adds-no-bend-logic
law copies.complete:
  for +cx: B.Cx
  for +o: U32
  for +i: B.In
  for +hi: {B.ins.has(B.ins.finals(B.cx.map(cx, o)), i) == True{} : Bool}
  for +he: {B.cp.ers(B.copies(cx, o)) == Nil{} : List<&2, B.Er>}
  {B.done.has(B.cp.done(B.copies(cx, o)), i) == True{} : Bool}

# LAW: and each instance the copies mark done has its copy among those
# they make, which become the object's units, one for each
# (`un.rds`): an instance is put in the set done with its copy added, in
# one step, and an empty set starts with no copies.
# Record: blend-adds-no-bend-logic
law copies.embodied:
  for +cx: B.Cx
  for +o: U32
  for +i: B.In
  for +hd: {B.done.has(B.cp.done(B.copies(cx, o)), i) == True{} : Bool}
  {B.rds.has(B.cp.rds(B.copies(cx, o)), i) == True{} : Bool}

# LAW: and where the copies report no error, every copy holds a
# definition named as its instance, never the placeholder a member not
# found would get: the member tables find only definitions of the name
# sought, and a member not found is an error (with `copies.embodied`,
# every instance done is a definition copied).
# Record: blend-adds-no-bend-logic
law copies.defined:
  for +cx: B.Cx
  for +o: U32
  for +he: {B.cp.ers(B.copies(cx, o)) == Nil{} : List<&2, B.Er>}
  {B.rds.defs(B.cp.rds(B.copies(cx, o))) == True{} : Bool}

# LAW: an object's member table finds what a search of its members
# finds, the first definition of the name sought, or none: a leaf keeps
# its entries in their order, and holds every definition whose name
# hashes there (`blend-scale.copies`), so that the copies find in it
# every definition the object has.
# Record: blend-adds-no-bend-logic
law members.indexed:
  for +ns: List<&2, B.Node>
  for +n: List<&2, U32>
  {B.md.find(B.md.table(ns), n) == B.mem.find(ns, n) : Maybe<&2, B.Node>}

# LAW: every object an entry of a fold names in its chain has a
# definition of the entry's name among its members, and no chain is
# empty: an entry is made by a member's definition and updated by one,
# so that an instance a chain gives, its final or a prior, has its
# member.
# Record: blend-adds-no-bend-logic
law folds.chained:
  for +ls: List<&2, Maybe<&2, B.Lz>>
  for +obs: List<&2, B.Ob>
  for +bad: List<&2, U32>
  {B.fds.chained(B.folds(ls, obs, bad), obs) == True{} : Bool}

# LAW: and so, in the context emission builds, every copy an object's
# copies make holds a definition named as its instance, no error
# assumed: every instance the copies take has its member, the finals'
# objects their chains' heads, a prior's in the chain of the entry its
# name finds, and the member tables find what the members' search finds
# (`members.indexed`); so `copies.defined`'s error never fires.
# Record: blend-adds-no-bend-logic
law copies.found:
  for +ls: List<&2, Maybe<&2, B.Lz>>
  for +obs: List<&2, B.Ob>
  for +bad: List<&2, U32>
  for +als: List<&2, B.Al>
  for +paths: List<&2, List<&2, U32>>
  for +pss: List<&2, List<&2, U32>>
  for +o: U32
  {B.rds.defs(B.cp.rds(B.copies(B.cx.of(obs, ls, B.folds(ls, obs, bad), als, paths, pss), o))) == True{} : Bool}

# LAW: every object's members, the made objects' included, are
# definitions the modules' trees hold: an object's members its node's in
# the tree, a made object's none or a mixin's.
# Record: blend-adds-no-bend-logic
law nodes.objects:
  for +trees: List<&2, List<&2, B.Node>>
  for +als: List<&2, B.Al>
  {B.objs.within(B.obs.made(B.syn.of(als, B.obs(trees))), B.trees.defs(trees)) == True{} : Bool}

# LAW: so every unit a module's objects copy has, where its definition is
# found, a definition the modules' trees hold, as they were read: the
# objects choose among definitions, and make none.
# Record: blend-adds-no-bend-logic
law nodes:
  for +trees: List<&2, List<&2, B.Node>>
  for +als: List<&2, B.Al>
  for +ls: List<&2, Maybe<&2, B.Lz>>
  for +fs: List<&2, Maybe<&2, B.Fd>>
  for +als2: List<&2, B.Al>
  for +paths: List<&2, List<&2, U32>>
  for +pss: List<&2, List<&2, U32>>
  {B.units.held(B.units(B.module.copies(B.obs.made(B.syn.of(als, B.obs(trees))),
    B.cx.of(B.obs.made(B.syn.of(als, B.obs(trees))), ls, fs, als2, paths, pss))),
    B.trees.defs(trees)) == True{} : Bool}

# LAW: items whose bodies are numbered on from their headers make a tree
# whose definitions keep them so, each a node of the object it is read
# in.
# Record: blend-adds-no-bend-logic
law markers.tree:
  for +its: List<&2, B.Item>
  for +h: {B.items.ok(its) == True{} : Bool}
  {B.defs.ok(B.tree(its)) == True{} : Bool}

# LAW: so a file read: every definition's body numbered on from its
# header's line, as a marker counts on.
# Record: blend-adds-no-bend-logic
law markers.read:
  for +bs: List<&2, U32>
  for +base: B.Loc
  {B.defs.ok(B.read.at(bs, base)) == True{} : Bool}

# LAW: and the units copied from trees so numbered, each where its
# definition is found, have their lines numbered on from their
# definition's line (or the line after): its body's, line for line,
# whatever object holds it.
# Record: blend-adds-no-bend-logic
law markers.units:
  for +trees: List<&2, List<&2, B.Node>>
  for +als: List<&2, B.Al>
  for +ls: List<&2, Maybe<&2, B.Lz>>
  for +fs: List<&2, Maybe<&2, B.Fd>>
  for +als2: List<&2, B.Al>
  for +paths: List<&2, List<&2, U32>>
  for +pss: List<&2, List<&2, U32>>
  for +h: {B.trees.ok(trees) == True{} : Bool}
  {B.units.ok(B.units(B.module.copies(B.obs.made(B.syn.of(als, B.obs(trees))),
    B.cx.of(B.obs.made(B.syn.of(als, B.obs(trees))), ls, fs, als2, paths, pss)))) == True{} : Bool}

# LAW: a unit's copy is written as where.sh reads it: after a newline,
# the marker's line naming its definition's file and line; after
# another, its header's line; then each of its body's lines, numbered on
# from the header's line (`markers.units`), on the line as many below the
# header's (the first on the header's own where numbered as it), its
# text after a newline of its own, holding none; where what it reads
# from its context holds none (`ec.inline`). So the line k below the
# marker is the source's k below the line the marker names.
# Record: blend-adds-no-bend-logic
law markers.writer:
  for +e: B.Ec
  for +s: U32
  for +x: U32
  for +j: U32
  for +b: B.Tb
  for +hf: {B.ec.inline(e) == True{} : Bool}
  for +hl: {B.rls.from(B.un.lines(B.ec.un(e, s)), B.node.no(B.un.node(B.ec.un(e, s)))) == True{} : Bool}
  {B.wr.unit(e, s, x, j, b) == True{} : Bool}

# LAW: a witness's copy, a witness having no body lines, is its head,
# then on its header's line a space and the witness's line, then a
# newline: so where Bend refuses a witness, at that line, where.sh names
# the declaration it checks, as the header's marker names it
# (`markers.writer`).
# Record: blend-declares-witnessed
law markers.witness:
  for +e: B.Ec
  for +x: U32
  for +j: U32
  for +b: B.Tb
  for +hw: {B.node.what(B.un.node(B.ec.un(e, x))) == 4 : U32}
  for +hl: {B.un.lines(B.ec.un(e, x)) == Nil{} : List<&2, B.Rl>}
  {B.tb.acc(B.unit.put(e, x, j, b)) == B.rev.onto(Con{32, List.append(&2, U32, B.wit.line(e, x), [10])}, B.tb.acc(B.unit.head(e, x, x, j, b))) : List<&2, U32>}

# LAW: and no line of a unit's copy after its marker's is one where.sh
# reads as a marker, as each line ends: its header's begins with `def` or
# `law`, and each body line on its own begins after a newline with its
# depth in spaces, or is empty; where the unit's lines are blank or
# deeper than its header but a first numbered as the header, kept on the
# header's line (`rl.deep`, `deep.units`), and what the writer reads from
# its context holds no newline (`ec.inline`). So the nearest marker above
# each of its lines is its definition's.
# Record: blend-adds-no-bend-logic
law markers.unambiguous:
  for +e: B.Ec
  for +s: U32
  for +x: U32
  for +j: U32
  for +b: B.Tb
  for +hf: {B.ec.inline(e) == True{} : Bool}
  for +hd: {B.rl.deep(B.un.lines(B.ec.un(e, s)), B.node.no(B.un.node(B.ec.un(e, s))), B.node.ind(B.un.node(B.ec.un(e, s))), True{}) == True{} : Bool}
  {B.wr.clear(e, s, x, j, b) == True{} : Bool}

# LAW: the datatypes of the code's file as where.sh reads them: split at
# its newlines, their text is an empty line, then for each datatype its
# marker's line naming its first line, its lines below as read, then an
# empty line (`dts.lines`), none of those lines beginning with `#`
# (`dts.clear`); where each datatype's lines are numbered on from its
# line, the first its `type` header, the rest blank or deeper, each
# within a line (`bend.ok`), and the files' names hold no newline. So the
# line k below a datatype's marker is the source's k - 1 below the line
# it names, and no line of a datatype reads as a marker.
# Record: blend-adds-no-bend-logic
law markers.datatypes:
  for +ns: List<&2, B.Node>
  for +files: List<&2, List<&2, U32>>
  for +hf: {B.inlines(files) == True{} : Bool}
  for +hb: {B.nodes.bend(ns) == True{} : Bool}
  {B.dts.where(ns, files) == True{} : Bool}

# LAW: a file's lines hold no newline: it splits them there.
# Record: blend-adds-no-bend-logic
law inline.lines:
  for +bs: List<&2, U32>
  for +base: B.Loc
  {B.lns.inline(B.lines.at(bs, base)) == True{} : Bool}

# LAW: lines holding no newline read as items whose texts hold none: a
# definition's name, the rest of its header and its body's lines, an
# object's name, an import's text, each part of a line or a literal.
# Record: blend-adds-no-bend-logic
law inline.items:
  for +ls: List<&2, B.Ln>
  for +h: {B.lns.inline(ls) == True{} : Bool}
  {B.items.inline(B.flat(ls)) == True{} : Bool}

# LAW: and such items make a tree whose texts hold none, a body's tokens
# spelling its lines (`tokens.spell`).
# Record: blend-adds-no-bend-logic
law inline.tree:
  for +its: List<&2, B.Item>
  for +h: {B.items.inline(its) == True{} : Bool}
  {B.nodes.inline(B.tree(its)) == True{} : Bool}

# LAW: so a file read gives the writer no newline within a line from
# its definitions, objects and imports (`markers.writer`'s `ec.inline`
# where they make its context).
# Record: blend-adds-no-bend-logic
law inline.read:
  for +bs: List<&2, U32>
  for +base: B.Loc
  {B.nodes.inline(B.read.at(bs, base)) == True{} : Bool}

# LAW: the objects made from trees whose texts hold no newline have paths
# holding none: each object's name joined to its host's path, a made
# object's name its mixin's, a copy's path its template's.
# Record: blend-adds-no-bend-logic
law inline.objects:
  for +trees: List<&2, List<&2, B.Node>>
  for +als: List<&2, B.Al>
  for +h: {B.trees.inline(trees) == True{} : Bool}
  {B.obs.inline(B.obs.made(B.syn.of(als, B.obs(trees)))) == True{} : Bool}

# LAW: the units copied from such objects, where the folds' maps name
# definitions within a line, have names, heads and lines holding no
# newline: each unit's definition one the trees hold (`nodes`), its
# tokens resolved as written or to parts of its names.
# Record: blend-adds-no-bend-logic
law inline.units:
  for +trees: List<&2, List<&2, B.Node>>
  for +als: List<&2, B.Al>
  for +ls: List<&2, Maybe<&2, B.Lz>>
  for +fs: List<&2, Maybe<&2, B.Fd>>
  for +als2: List<&2, B.Al>
  for +paths: List<&2, List<&2, U32>>
  for +pss: List<&2, List<&2, U32>>
  for +h: {B.trees.inline(trees) == True{} : Bool}
  for +hf: {B.fds.inline(fs) == True{} : Bool}
  {B.uns.inline(B.units(B.module.copies(B.obs.made(B.syn.of(als, B.obs(trees))),
    B.cx.of(B.obs.made(B.syn.of(als, B.obs(trees))), ls, fs, als2, paths, pss)))) == True{} : Bool}

# LAW: the objects made from trees whose texts hold no newline have
# members holding none: each object's its node's, a copy's its
# template's, a made object's none.
# Record: blend-adds-no-bend-logic
law inline.members:
  for +trees: List<&2, List<&2, B.Node>>
  for +als: List<&2, B.Al>
  for +h: {B.trees.inline(trees) == True{} : Bool}
  {B.obs.mems.inline(B.obs.made(B.syn.of(als, B.obs(trees)))) == True{} : Bool}

# LAW: and the folds of objects whose members hold no newline make maps
# of names holding none: each entry a member's name.
# Record: blend-adds-no-bend-logic
law inline.folds:
  for +ls: List<&2, Maybe<&2, B.Lz>>
  for +obs: List<&2, B.Ob>
  for +bad: List<&2, U32>
  for +h: {B.obs.mems.inline(obs) == True{} : Bool}
  {B.fds.inline(B.folds(ls, obs, bad)) == True{} : Bool}

# LAW: the imports read from members holding no newline give aliases
# holding none, each a part of its line.
# Record: blend-adds-no-bend-logic
law inline.own:
  for +ns: List<&2, B.Node>
  for +mpath: List<&2, U32>
  for +h: {B.nodes.inline(ns) == True{} : Bool}
  {B.cis.inline(B.cis.of(B.ims.of(ns), mpath)) == True{} : Bool}

# LAW: a table of a file's units, of units holding no newline, holds
# none.
# Record: blend-adds-no-bend-logic
law inline.table:
  for +us: List<&2, B.Un>
  for +laws: Bool
  for +h: {B.uns.inline(us) == True{} : Bool}
  {B.ht.inline(B.pt.of(B.Un, B.units.of(us, laws))) == True{} : Bool}

# LAW: modules whose paths hold no newline are named, in markers, by
# paths holding none: parts of theirs, and `..`.
# Record: blend-paths-no-newline
law inline.files:
  for +ms: List<&2, B.Md>
  for +root: List<&2, U32>
  for +h: {B.mds.inline(ms) == True{} : Bool}
  {B.inlines(B.mds.names(ms, root)) == True{} : Bool}

# LAW: an import Blend reads as local stays within its importer's
# directory, no part of its path `..` and none from `/`, so that a
# directory holds all its modules import and may be shared as a package.
# Record: blend-imports-local
law imports.local:
  for +p: List<&2, U32>
  for +ext: List<&2, U32>
  for +h: {B.import.plain(p, ext) == True{} : Bool}
  {B.path.down(B.split.slash(p, Nil{}, Nil{})) == True{} : Bool}

# LAW: a package's import keeps its path as written among its importer's
# imports, never joined to the importer's directory: Bend's to find.
# Record: blend-imports-local
law imports.package:
  for +mpath: List<&2, U32>
  for +p: List<&2, U32>
  for +alias: List<&2, U32>
  for +blend: Bool
  for +no: B.Loc
  for +h: {B.path.pkg(p) == True{} : Bool}
  {B.cis.of(Con{B.Im{p, alias, blend, no}, Nil{}}, mpath) == Con{B.Ci{alias, p, no}, Nil{}} : List<&2, B.Ci>}

# LAW: and re-imported into the root's file, for the bodies it copies,
# a package's import keeps its path as written.
# Record: blend-imports-local
law imports.package.root:
  for +root: List<&2, U32>
  for +p: List<&2, U32>
  for +h: {B.path.pkg(p) == True{} : Bool}
  {B.rel.import(root, p) == p : List<&2, U32>}

# LAW: a module whose path holds no newline imports modules whose paths
# hold none: an import's path is its line's, joined to its importer's.
# So, with a path from the command line refused where it holds one,
# every module read has a path holding none (`load.go`, by inspection).
# Record: blend-paths-no-newline
law inline.imports:
  for +path: List<&2, U32>
  for +bs: List<&2, U32>
  for +k: U32
  for +h: {B.inline(path) == True{} : Bool}
  {B.tds.inline(B.md.next(path, bs, k)) == True{} : Bool}

# LAW: so the context emission gives the writer, for the code's file
# and for the laws' and proofs' (`emitted`, `proof.parts`), holds no
# newline where its files' names hold none (`inline.files`): its
# objects' paths, its imports' aliases, its units' names and tokens;
# `markers.writer`'s hypothesis discharged. As `objects` makes the
# objects and the folds and `emitted` the table, composed as they
# compose them.
# Record: blend-adds-no-bend-logic
law markers.inline:
  for +files: List<&2, List<&2, U32>>
  for +trees: List<&2, List<&2, B.Node>>
  for +als: List<&2, B.Al>
  for +paths: List<&2, List<&2, U32>>
  for +us: List<&2, B.Un>
  for +res: List<&2, List<&2, U32>>
  for +mode: U32
  for +rtypes: List<&2, List<&2, U32>>
  for +ux: B.Ht<B.Xe>
  for +mt: B.Ht<B.Pk<B.Mu>>
  for +laws: Bool
  for +hf: {B.inlines(files) == True{} : Bool}
  for +ht: {B.trees.inline(trees) == True{} : Bool}
  {B.ec.inline(B.Ec{files, B.cx.obs(B.objects.cx(als, paths, B.obs(trees))), us, als,
    B.emit.own(B.objects.cx(als, paths, B.obs(trees))),
    res, paths, mode, rtypes, ux,
    B.pt.of(B.Un, B.units.of(B.units(B.module.copies(B.cx.obs(B.objects.cx(als, paths, B.obs(trees))),
      B.objects.cx(als, paths, B.obs(trees)))), laws)), mt}) == True{} : Bool}

# LAW: two definitions the same field by field (`ndef.same`) are equal,
# as two names the same are (`names.same_eq`): so a unit's definition
# held by the trees' (`nodes`) is one of them, and what holds of every
# tree's definition holds of every unit's.
# Record: blend-adds-no-bend-logic
law nodes.same_eq:
  for +a: B.Node
  for +b: B.Node
  for h: {B.ndef.same(a, b) == True{} : Bool}
  {a == b : B.Node}

# LAW: resolution makes no names: a token resolves to itself, as
# written, or to references and priors named by its text, a suffix of it
# (a mark dropped, a dotted name's last parts), or such a suffix and
# `#` (a law's proof), as `nodes` says the objects make no definitions.
# Record: blend-adds-no-bend-logic
law resolve.names:
  for +cx: B.Cx
  for +o: U32
  for +q: U32
  for +locals: List<&2, List<&2, U32>>
  for +t: B.Tok
  for +no: B.Loc
  {B.rr.made(B.rr.of(cx, o, q, locals, t, no), t) == True{} : Bool}

# LAW: the units' table holds the units' list by position: a lookup at i
# finds the list's unit at i, none past its end, each entry keyed by its
# position (`blend-units-keyed`); so a law over the units' list reaches
# what emission reads through its table.
# Record: blend-units-keyed
law units.positions:
  for +us: List<&2, B.Un>
  for +i: U32
  {B.ut.un(B.pt.of(B.Un, us), i) == B.un.at(us, i) : B.Un}

# LAW: so every unit emission writes, for the code's file or the laws'
# and proofs', is written as where.sh reads it (`markers.writer`): its
# context holding no newline (`markers.inline`), its lines numbered on
# from its definition's (`markers.units`), the table finding the units'
# own (`units.positions`). Its hypotheses the reader's alone: the files'
# names (`inline.files`), the trees as read (`inline.read`,
# `markers.read`).
# Record: blend-adds-no-bend-logic
law markers.emitted:
  for +files: List<&2, List<&2, U32>>
  for +trees: List<&2, List<&2, B.Node>>
  for +als: List<&2, B.Al>
  for +paths: List<&2, List<&2, U32>>
  for +us: List<&2, B.Un>
  for +res: List<&2, List<&2, U32>>
  for +mode: U32
  for +rtypes: List<&2, List<&2, U32>>
  for +ux: B.Ht<B.Xe>
  for +mt: B.Ht<B.Pk<B.Mu>>
  for +laws: Bool
  for +s: U32
  for +x: U32
  for +j: U32
  for +b: B.Tb
  for +hf: {B.inlines(files) == True{} : Bool}
  for +ht: {B.trees.inline(trees) == True{} : Bool}
  for +hk: {B.trees.ok(trees) == True{} : Bool}
  {B.wr.unit(B.Ec{files, B.cx.obs(B.objects.cx(als, paths, B.obs(trees))), us, als,
    B.emit.own(B.objects.cx(als, paths, B.obs(trees))),
    res, paths, mode, rtypes, ux,
    B.pt.of(B.Un, B.units.of(B.units(B.module.copies(B.cx.obs(B.objects.cx(als, paths, B.obs(trees))),
      B.objects.cx(als, paths, B.obs(trees)))), laws)), mt}, s, x, j, b) == True{} : Bool}

# LAW: so every unit emission writes, for the code's file or the laws'
# and proofs', any unit read, any copy, any text before it, has no line
# after its marker's that where.sh reads as a marker
# (`markers.unambiguous`): its hypotheses the reader's alone (the files'
# names, `inline.files`; the trees as read, `inline.read` and
# `deep.read`). With `markers.emitted`, the nearest marker above each
# line of a definition is its own, naming its line.
# Record: blend-adds-no-bend-logic
law unambiguous.emitted:
  for +files: List<&2, List<&2, U32>>
  for +trees: List<&2, List<&2, B.Node>>
  for +als: List<&2, B.Al>
  for +paths: List<&2, List<&2, U32>>
  for +us: List<&2, B.Un>
  for +res: List<&2, List<&2, U32>>
  for +mode: U32
  for +rtypes: List<&2, List<&2, U32>>
  for +ux: B.Ht<B.Xe>
  for +mt: B.Ht<B.Pk<B.Mu>>
  for +laws: Bool
  for +s: U32
  for +x: U32
  for +j: U32
  for +b: B.Tb
  for +hf: {B.inlines(files) == True{} : Bool}
  for +ht: {B.trees.inline(trees) == True{} : Bool}
  for +hd: {B.trees.deep(trees) == True{} : Bool}
  {B.wr.clear(B.Ec{files, B.cx.obs(B.objects.cx(als, paths, B.obs(trees))), us, als,
    B.emit.own(B.objects.cx(als, paths, B.obs(trees))),
    res, paths, mode, rtypes, ux,
    B.pt.of(B.Un, B.units.of(B.units(B.module.copies(B.cx.obs(B.objects.cx(als, paths, B.obs(trees))),
      B.objects.cx(als, paths, B.obs(trees)))), laws)), mt}, s, x, j, b) == True{} : Bool}

# LAW: so in the code's file as emitted, each copied unit of the walk's
# order ends with its counter one more than its numbered copies, each
# numbered copy one caller (`sharing.copied`), its hypotheses met by
# emission's own parts: the walk's order after its callees and once
# (`order.fast`, `order.callees_first`, `order.once`), the dispositions
# `mults` makes, and the writer reading the uses `mults` reads, its
# table the units' list's (`units.positions`). The units, their index,
# the roots and the rest of the context are any.
# Record: blend-copies-keep-their-name
law sharing.emitted:
  for +files: List<&2, List<&2, U32>>
  for +obs: List<&2, B.Ob>
  for +us: List<&2, B.Un>
  for +als: List<&2, B.Al>
  for +own: List<&2, B.Ci>
  for +res: List<&2, List<&2, U32>>
  for +paths: List<&2, List<&2, U32>>
  for +ux: B.Ht<B.Xe>
  for +roots: List<&2, U32>
  for +acc: List<&2, U32>
  for +y: U32
  for +hy: {B.has(B.ce.order(B.emit.code(files, obs, us, als, own, res, paths, ux, roots)), y) == True{} : Bool}
  for +hc: {B.mult.share(y, B.pt.of(B.Un, us)) == 2 : U32}
  {B.ctr.at(B.tb.ctrs(B.module.table(B.ce.e(B.emit.code(files, obs, us, als, own, res, paths, ux, roots)), B.ce.order(B.emit.code(files, obs, us, als, own, res, paths, ux, roots)), acc)), y) == U32.add(1, B.mu.m(B.ec.mu(B.ce.e(B.emit.code(files, obs, us, als, own, res, paths, ux, roots)), y))) : U32}

# LAW: a unit shared, or a module's definition (shared as Bend's), keeps
# its disposition through every unit's turn: its own leaves it as it is,
# another's touches only its own.
# Record: blend-module-is-bend, blend-copies-keep-their-name
law mults.shared:
  for +xs: List<&2, U32>
  for +rt: B.Ht<B.Pk<List<&2, B.Ru>>>
  for +ut: B.Ht<B.Pk<B.Un>>
  for +obs: List<&2, B.Ob>
  for +us: List<&2, B.Un>
  for +s: B.Ms
  for +p: B.Ht<B.Pk<List<&2, B.Ru>>>
  for +y: U32
  for +hs: {B.mult.share(y, ut) == 1 : U32}
  {B.ms.mu(B.mults(xs, rt, ut, obs, us, s, p), y) == B.ms.mu(s, y) : B.Mu}

# LAW: writing an order into the code's file, a plain unit's counter of
# numbered calls is never advanced: a call to it writes its own name, and
# a call to another advances that one's alone.
# Record: blend-copies-keep-their-name
law sharing.plain:
  for +xs: List<&2, U32>
  for +e: B.Ec
  for +b: B.Tb
  for +y: U32
  for +hm: {B.ec.mode(e) == 0 : U32}
  for +hk: {B.mu.kind(B.ec.mu(e, y)) == 0 : U32}
  {B.ctr.at(B.tb.ctrs(B.order.put(xs, e, b)), y) == B.ctr.at(B.tb.ctrs(b), y) : U32}

# LAW: so in the code's file as emitted, a unit shared, or a module's
# definition, is written once, by its own name, plain (`mults.shared`,
# the dispositions starting empty).
# Record: blend-module-is-bend, blend-copies-keep-their-name
law shared.emitted:
  for +files: List<&2, List<&2, U32>>
  for +obs: List<&2, B.Ob>
  for +us: List<&2, B.Un>
  for +als: List<&2, B.Al>
  for +own: List<&2, B.Ci>
  for +res: List<&2, List<&2, U32>>
  for +paths: List<&2, List<&2, U32>>
  for +ux: B.Ht<B.Xe>
  for +roots: List<&2, U32>
  for +y: U32
  for +hs: {B.mult.share(y, B.pt.of(B.Un, us)) == 1 : U32}
  {B.ec.mu(B.ce.e(B.emit.code(files, obs, us, als, own, res, paths, ux, roots)), y) == B.Mu{0, 0} : B.Mu}

# LAW: and every call to it names it: its counter of numbered calls ends
# where it starts, no numbered copy of it called (`sharing.plain`).
# Record: blend-module-is-bend, blend-copies-keep-their-name
law plain.emitted:
  for +files: List<&2, List<&2, U32>>
  for +obs: List<&2, B.Ob>
  for +us: List<&2, B.Un>
  for +als: List<&2, B.Al>
  for +own: List<&2, B.Ci>
  for +res: List<&2, List<&2, U32>>
  for +paths: List<&2, List<&2, U32>>
  for +ux: B.Ht<B.Xe>
  for +roots: List<&2, U32>
  for +acc: List<&2, U32>
  for +y: U32
  for +hs: {B.mult.share(y, B.pt.of(B.Un, us)) == 1 : U32}
  {B.ctr.at(B.tb.ctrs(B.module.table(B.ce.e(B.emit.code(files, obs, us, als, own, res, paths, ux, roots)), B.ce.order(B.emit.code(files, obs, us, als, own, res, paths, ux, roots)), acc)), y) == 1 : U32}

# LAW: where the laws' check reports no error, every law among the units
# has its proof: written beside the code (`blend-laws-in-module`), no law
# is left open to stop a run of the file.
# Record: blend-laws-in-module
law laws.proven:
  for +xs: List<&2, B.Un>
  for +ut: B.Ht<B.Pk<B.Un>>
  for +ux: B.Ht<B.Xe>
  for +h: {B.er.laws(xs, ut, ux) == Nil{} : List<&2, B.Er>}
  {B.laws.proven(xs, ux) == True{} : Bool}

# LAW: so where emission reports no error, every module has a proof for
# every law it writes, its units' table its own (`laws.proven`, the
# laws' check one part of emission's): one with none of laws, proofs or
# lemmas, whose check emission skips (`units.lawful`,
# `blend-perf.laws`), has none to prove. The walk's errors, the
# dispositions', the names' and the parts' are any.
# Record: blend-laws-in-module
law laws.emitted:
  for +dse: List<&2, B.Er>
  for +mse: List<&2, B.Er>
  for +all: List<&2, B.Un>
  for +order: List<&2, U32>
  for +e: B.Ec
  for +lwe: List<&2, B.Er>
  for +pfe: List<&2, B.Er>
  for +h: {B.emit.ers(dse, mse, all, order, e, lwe, pfe) == Nil{} : List<&2, B.Er>}
  {B.laws.proven(all, B.ux.of(all)) == True{} : Bool}

# LAW: and where emission reports no error, the definitions the code's
# file is written with (`module.table`, by `emit.defs` those of the
# walk's order reversed) are named each by a name of its own
# (`emit.unique`): emission checks the names of that order, in the
# context it writes. The errors of the walk, the dispositions, the laws
# and the proofs are any.
# Record: blend-namespaces-as-bends, blend-copies-keep-their-name
law unique.emitted:
  for +files: List<&2, List<&2, U32>>
  for +obs: List<&2, B.Ob>
  for +us: List<&2, B.Un>
  for +als: List<&2, B.Al>
  for +own: List<&2, B.Ci>
  for +res: List<&2, List<&2, U32>>
  for +paths: List<&2, List<&2, U32>>
  for +ux: B.Ht<B.Xe>
  for +roots: List<&2, U32>
  for +dse: List<&2, B.Er>
  for +mse: List<&2, B.Er>
  for +all: List<&2, B.Un>
  for +lwe: List<&2, B.Er>
  for +pfe: List<&2, B.Er>
  for +h: {B.emit.ers(dse, mse, all, B.ce.order(B.emit.code(files, obs, us, als, own, res, paths, ux, roots)), B.ce.e(B.emit.code(files, obs, us, als, own, res, paths, ux, roots)), lwe, pfe) == Nil{} : List<&2, B.Er>}
  {B.nms.distinct(B.defs.names(B.defs.of(List.reverse(&2, U32, B.ce.order(B.emit.code(files, obs, us, als, own, res, paths, ux, roots))), B.ce.e(B.emit.code(files, obs, us, als, own, res, paths, ux, roots))), B.ce.e(B.emit.code(files, obs, us, als, own, res, paths, ux, roots)))) == True{} : Bool}

# LAW: in the code's file as emitted, each copied unit of the walk's
# order has the copies its uses by the units written ask for, as the
# writer reads those uses and their users' copies (`sharing.final`): the
# dispositions `emitted` makes are those its writer's uses ask for.
# Record: blend-copies-keep-their-name
law final.emitted:
  for +files: List<&2, List<&2, U32>>
  for +obs: List<&2, B.Ob>
  for +us: List<&2, B.Un>
  for +als: List<&2, B.Al>
  for +own: List<&2, B.Ci>
  for +res: List<&2, List<&2, U32>>
  for +paths: List<&2, List<&2, U32>>
  for +ux: B.Ht<B.Xe>
  for +roots: List<&2, U32>
  for +y: U32
  for +hy: {B.has(B.ce.order(B.emit.code(files, obs, us, als, own, res, paths, ux, roots)), y) == True{} : Bool}
  for +hc: {B.mult.share(y, B.pt.of(B.Un, us)) == 2 : U32}
  {B.ec.mu(B.ce.e(B.emit.code(files, obs, us, als, own, res, paths, ux, roots)), y) == B.Mu{B.uses.m(B.uses.of.e(List.reverse(&2, U32, B.ce.order(B.emit.code(files, obs, us, als, own, res, paths, ux, roots))), B.ce.e(B.emit.code(files, obs, us, als, own, res, paths, ux, roots)), y), B.ec.ut(B.ce.e(B.emit.code(files, obs, us, als, own, res, paths, ux, roots))), B.ec.ms(B.ce.e(B.emit.code(files, obs, us, als, own, res, paths, ux, roots)))), 1} : B.Mu}

# LAW: and where the dispositions report no error, each affine unit of
# the walk's order is used once at most by the units written, as the
# writer reads their uses (`sharing.once`).
# Record: blend-copies-keep-their-name
law once.emitted:
  for +files: List<&2, List<&2, U32>>
  for +obs: List<&2, B.Ob>
  for +us: List<&2, B.Un>
  for +als: List<&2, B.Al>
  for +own: List<&2, B.Ci>
  for +res: List<&2, List<&2, U32>>
  for +paths: List<&2, List<&2, U32>>
  for +ux: B.Ht<B.Xe>
  for +roots: List<&2, U32>
  for +y: U32
  for +hy: {B.has(B.ce.order(B.emit.code(files, obs, us, als, own, res, paths, ux, roots)), y) == True{} : Bool}
  for +ha: {B.mult.share(y, B.pt.of(B.Un, us)) == 0 : U32}
  for +he: {B.ce.mers(B.emit.code(files, obs, us, als, own, res, paths, ux, roots)) == Nil{} : List<&2, B.Er>}
  {Nat.is_le(List.length(&2, B.Ru, B.uses.of.e(List.reverse(&2, U32, B.ce.order(B.emit.code(files, obs, us, als, own, res, paths, ux, roots))), B.ce.e(B.emit.code(files, obs, us, als, own, res, paths, ux, roots)), y)), 1n) == True{} : Bool}

# LAW: and an affine unit of the walk's order used once by the units
# written, as the writer reads their uses, ends with its user's copies,
# of the affine kind where there are any, else with none
# (`sharing.affine`).
# Record: blend-copies-keep-their-name
law affine.emitted:
  for +files: List<&2, List<&2, U32>>
  for +obs: List<&2, B.Ob>
  for +us: List<&2, B.Un>
  for +als: List<&2, B.Al>
  for +own: List<&2, B.Ci>
  for +res: List<&2, List<&2, U32>>
  for +paths: List<&2, List<&2, U32>>
  for +ux: B.Ht<B.Xe>
  for +roots: List<&2, U32>
  for +y: U32
  for +hy: {B.has(B.ce.order(B.emit.code(files, obs, us, als, own, res, paths, ux, roots)), y) == True{} : Bool}
  for +ha: {B.mult.share(y, B.pt.of(B.Un, us)) == 0 : U32}
  for +hl: {List.length(&2, B.Ru, B.uses.of.e(List.reverse(&2, U32, B.ce.order(B.emit.code(files, obs, us, als, own, res, paths, ux, roots))), B.ce.e(B.emit.code(files, obs, us, als, own, res, paths, ux, roots)), y)) == 1n : Nat}
  {B.ec.mu(B.ce.e(B.emit.code(files, obs, us, als, own, res, paths, ux, roots)), y) == B.mu.after(B.mu.m(B.ec.mu(B.ce.e(B.emit.code(files, obs, us, als, own, res, paths, ux, roots)), B.ru.user(B.uses.of.e(List.reverse(&2, U32, B.ce.order(B.emit.code(files, obs, us, als, own, res, paths, ux, roots))), B.ce.e(B.emit.code(files, obs, us, als, own, res, paths, ux, roots)), y)))), B.Mu{0, 0}) : B.Mu}

# LAW: errors reach the output, stage by stage (`blend-no-silent-failures`):
# a command over the modules read succeeds only where reading them
# reported no error (`run.mods.q`, `load.ers`).
# Record: blend-no-silent-failures
law errors.read:
  for +cmd: U32
  for +q: List<&2, U32>
  for +r: B.Md
  for +t: List<&2, B.Md>
  for +h: {B.out.ok(B.run.mods.q(cmd, q, Con{r, t})) == True{} : Bool}
  {B.load.ers(r, t) == Nil{} : List<&2, B.Er>}

# LAW: and over the modules' trees, only where the objects stage's
# checks reported none, every check of its context (`objects.ers`).
# Record: blend-no-silent-failures
law errors.objects:
  for +cmd: U32
  for +files: List<&2, List<&2, U32>>
  for +srcs: List<&2, List<&2, U32>>
  for +q: List<&2, U32>
  for +paths: List<&2, List<&2, U32>>
  for +trees: List<&2, List<&2, B.Node>>
  for +h: {B.out.ok(B.objects(cmd, files, srcs, q, paths, trees)) == True{} : Bool}
  {B.objects.ers(B.als.all(trees, 0, paths, B.obs(trees)), B.objects.cx(B.als.all(trees, 0, paths, B.obs(trees)), paths, B.obs(trees))) == Nil{} : List<&2, B.Er>}

# LAW: and past the objects, only where the copies reported none
# (`resolved.next`, `ocs.ers`), whether shown or emitted.
# Record: blend-no-silent-failures
law errors.copies:
  for +cmd: U32
  for +files: List<&2, List<&2, U32>>
  for +srcs: List<&2, List<&2, U32>>
  for +cx: B.Cx
  for +os: List<&2, B.Oc>
  for +h: {B.out.ok(B.resolved.next(cmd, files, srcs, cx, os)) == True{} : Bool}
  {B.ocs.ers(os) == Nil{} : List<&2, B.Er>}

# LAW: and emission writes its files only where its errors are none
# (`emit.out`). Which errors `emitted` gathers is
# `blend-laws2.named-builds.emission`'s.
# Record: blend-no-silent-failures
law errors.emitted:
  for +files: List<&2, List<&2, U32>>
  for +srcs: List<&2, List<&2, U32>>
  for +e: B.Ec
  for +order: List<&2, U32>
  for +tree: List<&2, B.Node>
  for +more: List<&2, U32>
  for +lw: B.Pf
  for +pf: B.Pf
  for +es: List<&2, B.Er>
  for +h: {B.out.ok(B.emit.out(files, srcs, e, order, tree, more, lw, pf, es)) == True{} : Bool}
  {es == Nil{} : List<&2, B.Er>}

# LAW: the reading's loops run on fuel enough (`blend-laws2.fuels`): the
# lines read into items take one turn each at most, a header taking its
# body, so that more fuel than lines changes nothing, and no line is
# ever dropped for want of it (`flat.go`).
# Record: blend-no-silent-failures
law flat.fuel:
  for +ls: List<&2, B.Ln>
  for +k: Nat
  {B.flat.go(Nat.add(k, List.length(&2, B.Ln, ls)), ls, Nil{}) == B.flat(ls) : List<&2, B.Item>}

# LAW: and objects closed take a frame each, so that more fuel than the
# stack's height changes nothing (`close.go`).
# Record: blend-no-silent-failures
law close.fuel:
  for +st: List<&2, B.Fr>
  for +i: U32
  for +k: Nat
  {B.close.go(Nat.add(k, List.length(&2, B.Fr, st)), st, i) == B.close(st, i) : List<&2, B.Fr>}

# LAW: and the objects made from the trees' member lists take a turn
# for each node and each list's end, so that more fuel than the turns a
# stack holds changes nothing (`obs.from`, `wf.turns`), no object
# dropped for want of it.
# Record: blend-no-silent-failures
law obs.fuel:
  for +st: List<&2, B.Wf>
  for +next: U32
  for +out: List<&2, B.Ob>
  for +k: Nat
  {B.obs.go(Nat.add(k, B.wf.turns(st)), st, next, out) == B.obs.from(st, next, out) : List<&2, B.Ob>}

# LAW: and an object's hosts take a turn for each number from its own
# down, where each object's host is itself or numbered no higher than
# its place (`er.hosts`, among the objects stage's errors), so that
# more fuel changes nothing (`hosts`), no host dropped for want of it.
# Record: blend-no-silent-failures
law hosts.fuel:
  for +obs: List<&2, B.Ob>
  for +id: U32
  for +k: Nat
  for +h: {B.er.hosts(obs, 0n) == Nil{} : List<&2, B.Er>}
  {B.hosts.go(Nat.add(k, 1n+U32.to_nat(id)), obs, id) == B.hosts(obs, id) : List<&2, U32>}

# LAW: and each of the objects stage's checks among its errors
# (`objects.ers`): where the stage reports none, none of its checks
# does, an object's host after it among them (`hosts.fuel`'s premise),
# so that no check drops out of the stage unseen
# (`blend-laws2.errors-reach`).
# Record: blend-no-silent-failures
law objects.checked:
  for +als: List<&2, B.Al>
  for +cx: B.Cx
  for +h: {B.objects.ers(als, cx) == Nil{} : List<&2, B.Er>}
  {Bool.and(List.is_empty(&2, B.Er, B.er.hosts(B.cx.obs(cx), 0n)),
    Bool.and(List.is_empty(&2, B.Er, B.er.endless(B.cx.pss(cx), B.cx.obs(cx))),
    Bool.and(List.is_empty(&2, B.Er, B.er.cycles(als, als)),
    Bool.and(List.is_empty(&2, B.Er, B.chains(B.cx.obs(cx), B.cx.obs(cx), B.cx.pss(cx))),
    Bool.and(List.is_empty(&2, B.Er, B.er.obs(B.cx.obs(cx), als, B.cx.obs(cx))),
    Bool.and(List.is_empty(&2, B.Er, B.er.made.parents(B.cx.obs(cx), als, B.cx.obs(cx), B.cx.ls(cx))),
    Bool.and(List.is_empty(&2, B.Er, B.er.lins(B.cx.pss(cx), B.cx.ls(cx), 0, B.cx.obs(cx), B.cx.ls(cx))),
    List.is_empty(&2, B.Er, B.er.defs(B.cx.pss(cx), B.cx.fs(cx), B.cx.ls(cx), 0, B.cx.obs(cx), B.cx.fs(cx)))))))))) == True{} : Bool}

# LAW: and the errors emission writes its files under are each of their
# parts' (`emitted.k`, `emitted.ers`): where it writes them, the walk
# reported none, nor the dispositions, the laws' check, the names',
# the laws' part, the proofs' part, nor a name Bend reserves, so that
# no part's errors drop out of emission unseen
# (`blend-laws2.errors-reach`).
# Record: blend-no-silent-failures
law emitted.checked:
  for +files: List<&2, List<&2, U32>>
  for +srcs: List<&2, List<&2, U32>>
  for +cx: B.Cx
  for +all: List<&2, B.Un>
  for +res: List<&2, List<&2, U32>>
  for +ce: B.Ce
  for +h: {B.out.ok(B.emitted.k(files, srcs, cx, all, res, ce)) == True{} : Bool}
  {Bool.and(List.is_empty(&2, B.Er, B.ce.wers(ce)),
    Bool.and(List.is_empty(&2, B.Er, B.ce.mers(ce)),
    Bool.and(List.is_empty(&2, B.Er, B.er.laws.if(B.units.lawful(all), all)),
    Bool.and(List.is_empty(&2, B.Er, B.er.names.of(B.names.all(List.reverse(&2, U32, B.ce.order(ce)), B.ce.e(ce)))),
    Bool.and(List.is_empty(&2, B.Er, B.pf.ers(B.proof.parts(1, files, cx, all, res))),
    Bool.and(List.is_empty(&2, B.Er, B.pf.ers(B.proof.parts(2, files, cx, all, res))),
    List.is_empty(&2, B.Er, B.er.reserved(B.names.all(List.reverse(&2, U32, B.ce.order(ce)), B.ce.e(ce)))))))))) == True{} : Bool}

# LAW: and each of the reading's checks among its errors (`load.ers`):
# where the reading reports none, no module an import reached went
# unread (`mds.ers`), and no module's imports have errors
# (`trees.plain.ers`), so that no check drops out of the reading unseen
# (`blend-laws2.errors-reach`).
# Record: blend-no-silent-failures
law read.checked:
  for +r: B.Md
  for +t: List<&2, B.Md>
  for +h: {B.load.ers(r, t) == Nil{} : List<&2, B.Er>}
  {Bool.and(List.is_empty(&2, B.Er, B.mds.ers(t, B.md.path(r))),
    List.is_empty(&2, B.Er, B.trees.plain.ers(B.mds.trees(Con{r, t}, 0)))) == True{} : Bool}

# LAW: and a module's imports checked each way (`trees.plain.ers`):
# where its imports and the later modules' report none, no path is one
# Bend would refuse (`ims.plain.ers`), no Blend module is imported
# without an alias (`ims.bare`), no alias names an earlier import or a
# name the module defines (`ims.fresh`), and the later modules' report
# none.
# Record: blend-no-silent-failures, blend-no-shadowing
law trees.checked:
  for +x: List<&2, B.Node>
  for +ts: List<&2, List<&2, B.Node>>
  for +h: {B.trees.plain.ers(Con{x, ts}) == Nil{} : List<&2, B.Er>}
  {Bool.and(List.is_empty(&2, B.Er, B.ims.plain.ers(B.ims.of(x))),
    Bool.and(List.is_empty(&2, B.Er, B.ims.bare(x)),
    Bool.and(List.is_empty(&2, B.Er, B.ims.fresh(B.ims.of(x), Nil{}, x)),
    List.is_empty(&2, B.Er, B.trees.plain.ers(ts))))) == True{} : Bool}

