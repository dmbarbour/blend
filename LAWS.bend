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
  for +ut: B.Ht<B.Pk<B.Un>>
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
  for +ut: B.Ht<B.Pk<B.Un>>
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
  for +hms: {B.ec.ms(e) == B.Ms{B.ms.ms(B.mults(xs, B.pw.of(List<&2, B.Ru>, rss), ut, obs, us, s, {B.WmNone{} : B.Wm<List<&2, B.Ru>>})), Nil{}} : B.Ms}
  for +hu: {B.uses.of.e(List.reverse(&2, U32, xs), e, y) == B.uses.of(List.reverse(&2, U32, xs), rss, y) : List<&2, B.Ru>}
  {B.ctr.at(B.tb.ctrs(B.order.put(List.reverse(&2, U32, xs), e, B.Tb{acc, B.WmNone{}})), y) == U32.add(1, B.mu.m(B.ec.mu(e, y))) : U32}

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
  for +base: U32
  {B.ln.from(B.lines.at(bs, base), (base + 1 : U32)) == True{} : Bool}

# LAW: lines numbered one more each read as items, each definition's body
# is the lines after its header's, none dropped nor merged, numbered on
# from its header's line (a type member's from that line itself), and a
# datatype's lines from its own: what a marker counts on.
# Record: blend-adds-no-bend-logic
law markers.items:
  for +ls: List<&2, B.Ln>
  for +k: U32
  for +h: {B.ln.from(ls, k) == True{} : Bool}
  {B.items.ok(B.flat(ls)) == True{} : Bool}

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
  for +nxs: List<&2, B.Ht<B.En>>
  for +ds: List<&2, B.Node>
  for +h: {B.objs.within(obs, ds) == True{} : Bool}
  {B.units.held(B.units(B.module.copies(obs, B.Cx{obs, ls, fs, als, paths, pss, nxs, B.mds.of(obs)})), ds) == True{} : Bool}

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
  for +nxs: List<&2, B.Ht<B.En>>
  {B.units.held(B.units(B.module.copies(B.obs.made(B.syn.of(als, B.obs(trees))),
    B.Cx{B.obs.made(B.syn.of(als, B.obs(trees))), ls, fs, als2, paths, pss, nxs, B.mds.of(B.obs.made(B.syn.of(als, B.obs(trees))))})),
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
  for +base: U32
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
  for +nxs: List<&2, B.Ht<B.En>>
  for +h: {B.trees.ok(trees) == True{} : Bool}
  {B.units.ok(B.units(B.module.copies(B.obs.made(B.syn.of(als, B.obs(trees))),
    B.Cx{B.obs.made(B.syn.of(als, B.obs(trees))), ls, fs, als2, paths, pss, nxs, B.mds.of(B.obs.made(B.syn.of(als, B.obs(trees))))}))) == True{} : Bool}

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

# LAW: a file's lines hold no newline: it splits them there.
# Record: blend-adds-no-bend-logic
law inline.lines:
  for +bs: List<&2, U32>
  for +base: U32
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
  for +base: U32
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
  for +nxs: List<&2, B.Ht<B.En>>
  for +h: {B.trees.inline(trees) == True{} : Bool}
  for +hf: {B.fds.inline(fs) == True{} : Bool}
  {B.uns.inline(B.units(B.module.copies(B.obs.made(B.syn.of(als, B.obs(trees))),
    B.Cx{B.obs.made(B.syn.of(als, B.obs(trees))), ls, fs, als2, paths, pss, nxs, B.mds.of(B.obs.made(B.syn.of(als, B.obs(trees))))}))) == True{} : Bool}

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
  for +mt: B.Wm<B.Mu>
  for +laws: Bool
  for +hf: {B.inlines(files) == True{} : Bool}
  for +ht: {B.trees.inline(trees) == True{} : Bool}
  {B.ec.inline(B.Ec{files, B.obs.made(B.syn.of(als, B.obs(trees))), us, als,
    B.emit.own(B.Cx{B.obs.made(B.syn.of(als, B.obs(trees))), B.sy.ls(B.syn.of(als, B.obs(trees))),
      B.folds(B.sy.ls(B.syn.of(als, B.obs(trees))), B.obs.made(B.syn.of(als, B.obs(trees))), B.chains.bad(B.obs.made(B.syn.of(als, B.obs(trees))), B.obs.made(B.syn.of(als, B.obs(trees))), B.sy.pss(B.syn.of(als, B.obs(trees))))),
      als, paths, B.sy.pss(B.syn.of(als, B.obs(trees))),
      B.nxs.of(B.folds(B.sy.ls(B.syn.of(als, B.obs(trees))), B.obs.made(B.syn.of(als, B.obs(trees))), B.chains.bad(B.obs.made(B.syn.of(als, B.obs(trees))), B.obs.made(B.syn.of(als, B.obs(trees))), B.sy.pss(B.syn.of(als, B.obs(trees)))))),
      B.mds.of(B.obs.made(B.syn.of(als, B.obs(trees))))}),
    res, paths, mode, rtypes, ux,
    B.pt.of(B.Un, B.units.of(B.units(B.module.copies(B.obs.made(B.syn.of(als, B.obs(trees))),
      B.Cx{B.obs.made(B.syn.of(als, B.obs(trees))), B.sy.ls(B.syn.of(als, B.obs(trees))),
        B.folds(B.sy.ls(B.syn.of(als, B.obs(trees))), B.obs.made(B.syn.of(als, B.obs(trees))), B.chains.bad(B.obs.made(B.syn.of(als, B.obs(trees))), B.obs.made(B.syn.of(als, B.obs(trees))), B.sy.pss(B.syn.of(als, B.obs(trees))))),
        als, paths, B.sy.pss(B.syn.of(als, B.obs(trees))),
        B.nxs.of(B.folds(B.sy.ls(B.syn.of(als, B.obs(trees))), B.obs.made(B.syn.of(als, B.obs(trees))), B.chains.bad(B.obs.made(B.syn.of(als, B.obs(trees))), B.obs.made(B.syn.of(als, B.obs(trees))), B.sy.pss(B.syn.of(als, B.obs(trees)))))),
        B.mds.of(B.obs.made(B.syn.of(als, B.obs(trees))))})), laws)), mt}) == True{} : Bool}

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
  for +no: U32
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
  for +mt: B.Wm<B.Mu>
  for +laws: Bool
  for +s: U32
  for +x: U32
  for +j: U32
  for +b: B.Tb
  for +hf: {B.inlines(files) == True{} : Bool}
  for +ht: {B.trees.inline(trees) == True{} : Bool}
  for +hk: {B.trees.ok(trees) == True{} : Bool}
  {B.wr.unit(B.Ec{files, B.obs.made(B.syn.of(als, B.obs(trees))), us, als,
    B.emit.own(B.Cx{B.obs.made(B.syn.of(als, B.obs(trees))), B.sy.ls(B.syn.of(als, B.obs(trees))),
      B.folds(B.sy.ls(B.syn.of(als, B.obs(trees))), B.obs.made(B.syn.of(als, B.obs(trees))), B.chains.bad(B.obs.made(B.syn.of(als, B.obs(trees))), B.obs.made(B.syn.of(als, B.obs(trees))), B.sy.pss(B.syn.of(als, B.obs(trees))))),
      als, paths, B.sy.pss(B.syn.of(als, B.obs(trees))),
      B.nxs.of(B.folds(B.sy.ls(B.syn.of(als, B.obs(trees))), B.obs.made(B.syn.of(als, B.obs(trees))), B.chains.bad(B.obs.made(B.syn.of(als, B.obs(trees))), B.obs.made(B.syn.of(als, B.obs(trees))), B.sy.pss(B.syn.of(als, B.obs(trees)))))),
      B.mds.of(B.obs.made(B.syn.of(als, B.obs(trees))))}),
    res, paths, mode, rtypes, ux,
    B.pt.of(B.Un, B.units.of(B.units(B.module.copies(B.obs.made(B.syn.of(als, B.obs(trees))),
      B.Cx{B.obs.made(B.syn.of(als, B.obs(trees))), B.sy.ls(B.syn.of(als, B.obs(trees))),
        B.folds(B.sy.ls(B.syn.of(als, B.obs(trees))), B.obs.made(B.syn.of(als, B.obs(trees))), B.chains.bad(B.obs.made(B.syn.of(als, B.obs(trees))), B.obs.made(B.syn.of(als, B.obs(trees))), B.sy.pss(B.syn.of(als, B.obs(trees))))),
        als, paths, B.sy.pss(B.syn.of(als, B.obs(trees))),
        B.nxs.of(B.folds(B.sy.ls(B.syn.of(als, B.obs(trees))), B.obs.made(B.syn.of(als, B.obs(trees))), B.chains.bad(B.obs.made(B.syn.of(als, B.obs(trees))), B.obs.made(B.syn.of(als, B.obs(trees))), B.sy.pss(B.syn.of(als, B.obs(trees)))))),
        B.mds.of(B.obs.made(B.syn.of(als, B.obs(trees))))})), laws)), mt}, s, x, j, b) == True{} : Bool}

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
  for +hy: {B.has(B.ds.order(B.emit.walk(roots, B.refss(us, ux, 0), obs, us)), y) == True{} : Bool}
  for +hc: {B.mult.share(y, B.pt.of(B.Un, us)) == 2 : U32}
  {B.ctr.at(B.tb.ctrs(B.module.table(B.emit.ec(files, obs, us, als, own, res, paths, ux, B.pt.of(B.Un, us), B.ms.ms(B.emit.ms(B.ds.order(B.emit.walk(roots, B.refss(us, ux, 0), obs, us)), B.refss(us, ux, 0), B.pt.of(B.Un, us), obs, us))), B.ds.order(B.emit.walk(roots, B.refss(us, ux, 0), obs, us)), acc)), y) == U32.add(1, B.mu.m(B.ec.mu(B.emit.ec(files, obs, us, als, own, res, paths, ux, B.pt.of(B.Un, us), B.ms.ms(B.emit.ms(B.ds.order(B.emit.walk(roots, B.refss(us, ux, 0), obs, us)), B.refss(us, ux, 0), B.pt.of(B.Un, us), obs, us))), y))) : U32}

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
  for +h: {B.emit.ers(dse, mse, all, B.ds.order(B.emit.walk(roots, B.refss(us, ux, 0), obs, us)), B.emit.ec(files, obs, us, als, own, res, paths, ux, B.pt.of(B.Un, us), B.ms.ms(B.emit.ms(B.ds.order(B.emit.walk(roots, B.refss(us, ux, 0), obs, us)), B.refss(us, ux, 0), B.pt.of(B.Un, us), obs, us))), lwe, pfe) == Nil{} : List<&2, B.Er>}
  {B.nms.distinct(B.defs.names(B.defs.of(List.reverse(&2, U32, B.ds.order(B.emit.walk(roots, B.refss(us, ux, 0), obs, us))), B.emit.ec(files, obs, us, als, own, res, paths, ux, B.pt.of(B.Un, us), B.ms.ms(B.emit.ms(B.ds.order(B.emit.walk(roots, B.refss(us, ux, 0), obs, us)), B.refss(us, ux, 0), B.pt.of(B.Un, us), obs, us)))), B.emit.ec(files, obs, us, als, own, res, paths, ux, B.pt.of(B.Un, us), B.ms.ms(B.emit.ms(B.ds.order(B.emit.walk(roots, B.refss(us, ux, 0), obs, us)), B.refss(us, ux, 0), B.pt.of(B.Un, us), obs, us))))) == True{} : Bool}

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
  for +hy: {B.has(B.ds.order(B.emit.walk(roots, B.refss(us, ux, 0), obs, us)), y) == True{} : Bool}
  for +hc: {B.mult.share(y, B.pt.of(B.Un, us)) == 2 : U32}
  {B.ec.mu(B.emit.ec(files, obs, us, als, own, res, paths, ux, B.pt.of(B.Un, us), B.ms.ms(B.emit.ms(B.ds.order(B.emit.walk(roots, B.refss(us, ux, 0), obs, us)), B.refss(us, ux, 0), B.pt.of(B.Un, us), obs, us))), y) == B.Mu{B.uses.m(B.uses.of.e(List.reverse(&2, U32, B.ds.order(B.emit.walk(roots, B.refss(us, ux, 0), obs, us))), B.emit.ec(files, obs, us, als, own, res, paths, ux, B.pt.of(B.Un, us), B.ms.ms(B.emit.ms(B.ds.order(B.emit.walk(roots, B.refss(us, ux, 0), obs, us)), B.refss(us, ux, 0), B.pt.of(B.Un, us), obs, us))), y), B.ec.ut(B.emit.ec(files, obs, us, als, own, res, paths, ux, B.pt.of(B.Un, us), B.ms.ms(B.emit.ms(B.ds.order(B.emit.walk(roots, B.refss(us, ux, 0), obs, us)), B.refss(us, ux, 0), B.pt.of(B.Un, us), obs, us)))), B.ec.ms(B.emit.ec(files, obs, us, als, own, res, paths, ux, B.pt.of(B.Un, us), B.ms.ms(B.emit.ms(B.ds.order(B.emit.walk(roots, B.refss(us, ux, 0), obs, us)), B.refss(us, ux, 0), B.pt.of(B.Un, us), obs, us))))), 1} : B.Mu}

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
  for +hy: {B.has(B.ds.order(B.emit.walk(roots, B.refss(us, ux, 0), obs, us)), y) == True{} : Bool}
  for +ha: {B.mult.share(y, B.pt.of(B.Un, us)) == 0 : U32}
  for +he: {B.ms.ers(B.emit.ms(B.ds.order(B.emit.walk(roots, B.refss(us, ux, 0), obs, us)), B.refss(us, ux, 0), B.pt.of(B.Un, us), obs, us)) == Nil{} : List<&2, B.Er>}
  {Nat.is_le(List.length(&2, B.Ru, B.uses.of.e(List.reverse(&2, U32, B.ds.order(B.emit.walk(roots, B.refss(us, ux, 0), obs, us))), B.emit.ec(files, obs, us, als, own, res, paths, ux, B.pt.of(B.Un, us), B.ms.ms(B.emit.ms(B.ds.order(B.emit.walk(roots, B.refss(us, ux, 0), obs, us)), B.refss(us, ux, 0), B.pt.of(B.Un, us), obs, us))), y)), 1n) == True{} : Bool}

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
  for +hy: {B.has(B.ds.order(B.emit.walk(roots, B.refss(us, ux, 0), obs, us)), y) == True{} : Bool}
  for +ha: {B.mult.share(y, B.pt.of(B.Un, us)) == 0 : U32}
  for +hl: {List.length(&2, B.Ru, B.uses.of.e(List.reverse(&2, U32, B.ds.order(B.emit.walk(roots, B.refss(us, ux, 0), obs, us))), B.emit.ec(files, obs, us, als, own, res, paths, ux, B.pt.of(B.Un, us), B.ms.ms(B.emit.ms(B.ds.order(B.emit.walk(roots, B.refss(us, ux, 0), obs, us)), B.refss(us, ux, 0), B.pt.of(B.Un, us), obs, us))), y)) == 1n : Nat}
  {B.ec.mu(B.emit.ec(files, obs, us, als, own, res, paths, ux, B.pt.of(B.Un, us), B.ms.ms(B.emit.ms(B.ds.order(B.emit.walk(roots, B.refss(us, ux, 0), obs, us)), B.refss(us, ux, 0), B.pt.of(B.Un, us), obs, us))), y) == B.mu.after(B.mu.m(B.ec.mu(B.emit.ec(files, obs, us, als, own, res, paths, ux, B.pt.of(B.Un, us), B.ms.ms(B.emit.ms(B.ds.order(B.emit.walk(roots, B.refss(us, ux, 0), obs, us)), B.refss(us, ux, 0), B.pt.of(B.Un, us), obs, us))), B.ru.user(B.uses.of.e(List.reverse(&2, U32, B.ds.order(B.emit.walk(roots, B.refss(us, ux, 0), obs, us))), B.emit.ec(files, obs, us, als, own, res, paths, ux, B.pt.of(B.Un, us), B.ms.ms(B.emit.ms(B.ds.order(B.emit.walk(roots, B.refss(us, ux, 0), obs, us)), B.refss(us, ux, 0), B.pt.of(B.Un, us), obs, us))), y)))), B.Mu{0, 0}) : B.Mu}
