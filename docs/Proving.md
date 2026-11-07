# Proving in Bend

What the laws and proofs written so far have taught, generic across proof
files. Bend's own shortfalls, with their upstream issues, are in
glam-in-bend's [BendIssues.md](https://github.com/dmbarbour/glam-in-bend/blob/main/docs/BendIssues.md); a proof file records in its header what
it alone taught. Add to this file what a new proof teaches.

## What to claim

- **The guarantees a user sees first**: what is emitted, kept or refused.
- **A weaker law, and its missing pieces.** A full claim can cost far more
  than it buys. It is often enough to prove that each step keeps some
  property under a reasonable precondition, then prove the precondition,
  or broaden it where that is not too hard. When you weaken a law, list
  what it no longer claims, and the separate laws that would bring it
  close enough, in the plan beside the law. A law that an order is
  callee-first wants laws that the order loses and duplicates nothing; a
  law that every item receives a disposition wants a law that every
  disposition is carried out (where no error is reported).
- **Confidence, not only cheapness.** A guard that makes a law hold by
  computation (AGENTS.md, Laws) is a fine shape, but prove too that the
  guard never fires where it should not, or say plainly that the law does
  not claim it. Once a stronger law proves a guard never fires, the guard
  is redundant work, not a boundary: remove it, and prove its law from
  the stronger one.
- **Termination where feasible.** A walk bounded by fuel can carry a law
  that a walk cut short reports an error; a proof that the fuel suffices
  is stronger, and often feasible by a potential (below). Try it before
  settling for the weaker law.
- **An invariant a walk hands on, as a function**: "every instance done
  has its copy" is `@h:{done.has(...)} -> {copied(...)}` for the state,
  each step building the next state's from the last's, which it uses
  once, and the recursion taking it as an argument (`cm_go`,
  `copies.embodied`); an empty start gives it by refutation.
- **A silent fallback made an error, its law claimed where none is
  reported**: `copy.of`'s placeholder for a member not found became an
  error, so that "every copy a definition" holds where the copies report
  none (`copies.defined`); errors only grow through the walk (`ers_back`,
  an induction mirroring it), so the result's none brings each step's.
  Proving the fallback never fires is a law of its own, the expensive
  half (`blend-laws2.copies-found`).
- **An invariant of a list kept beside its index**: where a step reads
  what it builds on from an index (the fold's `ix`) and writes the list
  (its map), the invariant holds of both (`fdok`), the trie's laws
  twinned for its predicate (`hch_put`, `hch_leaf`); a lookup's result
  is stated for the name sought (`mch`), so that no equation between
  the index and the list is needed (`folds.chained`).
- **A walk's twin for one field**: where only one branch of a walk makes
  the part a law is about (the copies' priors, `rr.prior.of`), the twin
  reuses the walk's mirrors and proves each other case by `{==}`
  (`copies.found`, after the `rril` walk).
- **A context's shape as an equation**: a lemma over a context built one
  way takes the shape as a hypothesis `{field(cx) == built(..)}`, which
  can be `+`-marked and handed through a recursion, where a function
  hypothesis is used once; the law, stating the context so, gives `{==}`
  (`cxmds`, `copies.found`).
- **Completeness where termination is out of reach**: a worklist whose
  pushes no potential bounds (the copies', which reach priors through
  bodies) runs on ample fuel and reports an error where it runs out with
  work left, so that the law claims completeness where no error is
  reported (`copies.complete`): the fuel's end refuted by the error's
  constructor, and the fuel's sufficiency listed as the missing piece.
- **Mutate the code after a proof passes**: break what the law is about
  in a copy, and see the proofs fail. A law that survives the mutation
  claims less than meant. Keep the mutations in a `MUTANTS.txt` beside
  the proof file (`X_MUTANTS.txt` beside `X_PROOF.bend`), each naming the
  laws it should fail: the gate tries each against them
  (`scripts/one_law.py`, below), its pass kept while its inputs are
  unchanged.

## Shaping the code a law follows

- **Test values; do not match literals.** A `U32` is a word of bits to
  Bend's proofs, so a match on literals (`case 46:` ... `case _:`)
  leaves the `_` case a word partly known, on which the function's own
  match is stuck. Test (`U32.is_eq(h, 46)`) and branch on the `Bool`.
- **A boundary tested apart costs its law an `and_l`.** Where a check
  implies a property only through its parts (no plain name is `..`), a
  test of the property beside it (`path.down`, `blend-imports-local`)
  makes the law read the test off the check. The mutants then catch the
  test's removal, never a fault in the test itself, which the plan
  lists as the law's missing piece.
- **A class of values is a datatype**, its tests `Bool`s: constructors
  match in proofs, literals do not.
- **Branch in a named helper matching its `Bool` parameters**
  (`f.k(+test: Bool, ...)`), the tests computed by its caller, so that a
  lemma about the helper splits the `Bool`s without restating lambdas,
  which Bend does not infer. A `when` with lambdas serves too, at the
  cost of a helper def in the proof file mirroring them, and of a
  closure for each arm at run time: in the hash trie's put and lookup,
  14 to 23% of Blend's instructions (`blend-laws.unique`).
- **A recursive decision on a test** whose arms recurse: Bend matches
  no local (`+c = test` then `match c`: "give it its own def"), a helper
  may not call back (no mutual recursion), and a self-call through a
  helper's result (`f(pick(c, z, o))`) is no structural descent. Recurse
  on fuel instead, matched first, and let non-recursive helpers decide
  on the `Bool` (`ht.pick`, `ht.join`): 3 to 5% in the trie.
- **A loop whose every arm recurses on the same tail is a step**: a
  non-recursive function deciding on the tests as `Bool` parameters
  returns the next state as a record, and the loop recurses once
  (`lines.step`). A `when` there costs two closures, a wrap of each
  value both capture, and a drop, at every turn: in `lines.go`, 8 to 10%
  of Blend's instructions (`blend-perf.lines`). A proof's mirror of
  the `when` becomes the step, its cases as before.
- **`&&` and `||` evaluate both sides** in a native build
  (`bench/andor.bend`; a benchmark clang can fold shows flat counts
  that look like short-circuiting, as one did on 2026-11-05), so a test
  guarding an expensive one (`mode == 2 && proves.own(...)`) does not
  spare it. Decide on the cheap test first, in a helper matching it
  (`ref.put.m`, `holds.at`): in the writer, 3 to 16% of Blend's
  instructions (`blend-perf.lookups`); in finding text within a line,
  up to 18% (`blend-perf.strict`).
- **A result read twice is a datatype read by projections**, not
  destructured in a lambda (`on.r(r, a => b => ...)`), which sticks a
  proof until the result reduces.
- **State whose invariant holds by computation**: then the law costs a
  case split per step.
- **Narrow a decision to where it can happen**: the writer kept on its
  header's line any line numbered as the header, a test that only the
  first line can pass, but that a proof must refute for every later
  line, past 2^32 lines too; tested on the first line alone
  (`rls.put`'s `first`), the later lines' newlines hold by computation
  (`markers.writer`).
- **Carry a second invariant in the relation a walk carries**: where a
  long walk (the copies') carries a relation between what it makes and
  what it read (`nos`, a unit's lines its body's number for number),
  strengthen the relation (`lk`: the same depth, a blank line blank)
  rather than walk again: only the lemmas that build and read it change
  (`deep.units`).
- **A predicate per invariant costs a copy of the makers' lemmas**: an
  invariant of items through every item maker (`deep.items` beside
  `markers.items`) wants each maker's lemma again, its mirror defs
  shared; derive the twins from the proved ones by renaming the
  predicate and the hypothesis, and write by hand only what differs.
- **Name a composite's parts to join laws at it**: a law cannot name
  a function's locals, so `emitted`'s walk, dispositions, writer's
  context, table and errors are definitions of their own (`emit.walk`,
  `emit.ms`, `emit.ec`, `module.table`, `emit.ers`), `emitted` calling
  each and the joined laws naming them (`sharing.emitted`,
  `unique.emitted`); a mutation of a part then fails the join, where a
  law restating the composition by hand would not see it. With one
  caller each they cost nothing, but pass a part the fields it reads,
  not the records holding them (AGENTS.md, Measuring).

## Writing proofs

- **A recursive proof never matches a computed value.** A non-recursive
  step lemma takes the `Bool` as a parameter, an equation tying it to its
  test, and every induction hypothesis the cases need, and splits it; the
  recursion stays in the caller, Bend having no mutual recursion.
- **`%e : P` rewrites with `e : {a == b}`**: the goal is `P` with `b`
  where `_` stands, and becomes `P` with `a`. State lemmas so that `a` is
  the simple form and `b` the complex one, so that a rewrite turns the
  complex form in a goal into the simple; wrap a lemma that runs the
  other way in `Equal.sym` once: `Equal.sym(T, a, b, e)` takes
  `e : {a == b}` and gives `{b == a}`. Every `_` in `P` is rewritten,
  so that one rewrite turns both sides of a goal.
- **Mark what a proof reuses**: `+` on a law's `for` binders, a proof's
  parameters and its patterns (`case Con{+h, +t}`, `case 1n+(+k)`).
- **An absurd case names its type**: `Empty.absurd(T, e)`, `T` written
  out; refute a clash of constructors through a motive sending one to
  `Unit` and the other to `Empty`. Where a hypothesis says a mirrored
  step is `Nil` and the step makes a `Con`, rewrite the mirror itself in
  the motive (`ers_some`), so that the `Con` need not be spelled out.
- **A big constant is reasoned under a variable** `N` with
  `{N == Nat.pow(2n, 32n)}`, the power met only against a symbolic value
  or where both forms match exactly (glam-in-bend's BendIssues.md, "Big
  constants in proofs"): a recursive lemma stating
  `Nat.mod(k, Nat.pow(2n, 32n))` overflowed Bend's checker, where one
  over a variable (`wrap_m`) did not.
- **A proof function is used once.** A function cannot be `+`-marked, so
  a lemma taking one (`@x:A -> P(x)`, Bend's dependent function) cannot
  both use it and pass it on. State a reusable fact as a `Bool`
  equation instead (containment as `all.in(xs, ys) == True`), and keep
  function arguments to a case split, each branch used once
  (`or_cases(a, b, c, h, fa, fb)`).
- **Several invariants as one `Bool`**: a conjunction `inv(s) == True`,
  with a lemma building it from its parts and one taking each part out
  (the hub's `eq_true_of_and_left`, `eq_true_of_and_right`), so that a
  step lemma takes and returns one equation.
- **Termination by a potential**: a `Nat` the state determines, what is
  left to do each counted by what it will cost, that each step lowers by
  one at least, under an invariant the steps keep. Give the walk that
  potential at the start as its fuel, and prove by induction on the fuel,
  from `le(pot(s), n)`, that it finishes: at `0n` the potential's being
  positive refutes the unfinished states. Over-approximate where exact
  costs more: a list of candidates, duplicates and all, each counted
  while not yet done, only overcounts, and makes a step's descent a lemma
  on one removal. But an overcount can make the fuel superlinear, and a
  walk run to its fuel pays all of it: count each item once by its
  index where an index exists, the index of a `U32` its `U32.to_nat`
  (the hub's `u32_is_eq_to_nat` ties `U32.is_eq` to it), and the
  potential needs no invariant naming the candidates.
- **Prove a fast version against a proved one.** Where a state's lists
  must become lookups, keep the proved code as the specification and
  run a version beside it that adds its indexes, then prove one law:
  dropping the indexes, its result is the specification's. Lift a
  specification state with the indexes its lists make; show that a step
  from a lifted state is the lifted step, for every state, no
  hypothesis; induct on the fuel. An index whose shape is a function of
  its set (a trie on a key's bits) makes the lift a computation, the
  lists' order aside: prove that putting commutes.
- **A hash trie keyed, proved as a map**: where a trie's path is a
  key's bits (shifts and masks the hub's `U32` laws do not reach), key
  each entry and let a lookup compare: a put at another key then leaves
  a lookup as it was whatever leaf it lands in (`put_else`, the
  descent's two tests split four ways), so no path arithmetic is
  needed (`units.positions`; `blend-units-keyed`). Its converse, a
  lookup after a put finds the entry put or one found before
  (`ins_split`, `copies.embodied`), splits the same four ways, the
  hypothesis carried across the bit's equation by `Equal.sym` of it.
- **A trie on a `U32`'s own word** (`U32{Word(32n)}`, the lowest bit
  first) is structural all the way down: a lookup and a put recurse on
  the word, and `Word.cmp`'s last step splits into the tails and the
  bits, so that no arithmetic, and no bound of 2^32, is met. A table by
  position is the same trie over a list split by its positions' bits:
  `List.get(xs, double(i))` and `List.get(xs, 1+double(i))`.
- **A specification sharing the decisions**: where a law pins an
  optimization, write the specification beside the code to share every
  function the optimization left alone, so that the law claims what
  changed and no more, and list what the shared functions decide among
  its missing pieces.
- **A law's proof may call another law's** (`Laws.x(...)`, typed by its
  law), so that a law for the case the tool meets composes the general
  law with the laws of what feeds it.
- **Peel an accumulator off by a twin**: where a loop accumulates its
  result (`c3.merge`'s `out`), prove it equal to its direct recursion
  after the accumulated prefix (`merge_acc`), and reason about the twin
  (`mrest`): each turn's result then sits before the rest's.
- **Completeness by a witness, not a cycle**: "fails only where no
  answer exists" is proved as "given an answer, succeeds", by induction
  on the answer given; for C3, the given order's first object that any
  list holds is a free head (`good_of`).
- **A predicate on a record's field** sticks where the field is a
  variable (`has_ers` on `Ms{ms, ers}`), though it reads that field
  alone: a lemma relating two records with the same field matches the
  field too (`set_ers`).
- **A pair taken apart by a lambda** (`on.pair(p, a => b => ...)`)
  sticks while `p` is computed: prove what is wanted of each half
  (`Pair.fst`, `Pair.snd`) by a lemma of its own, and rewrite by the
  pair's eta law, a match on the pair (`pair_eta`, `case (a, b):`),
  rather than pass the lambda's property in as a function, which the
  recursion would need twice.
- **Provenance, by membership**: "every unit's definition is one the
  tree holds" is stated as `Bool` membership under a structural `Bool`
  equality (`ndef.same`), with a "within" invariant kept by every
  builder on the way (`defs.within`, `objs.within`, a table's leaves
  `hw`). A generic form over any property is out of reach: a property
  is a function, which a recursion cannot both use and pass on. Prove
  the structural equality equality (`nodes.same_eq`): then each
  property crosses it by one rewrite (`same_ok`, `same_il`), where
  each took case work of its own.
- **Containment by a recursive `Bool`**: "a suffix of" stated as
  `suffix(p, xs)`, `p` is `xs` or a suffix of its tail, so that drops,
  tails and appends are each an induction (`suffix_drop`, `suffix_app`,
  `suffix_trans`), where `ends`, a drop by a difference of lengths,
  would want length arithmetic in every one (`resolve.names`).
- **Name a function's locals to state them**: a law cannot name a
  `+x = ...` inside a definition; making the local a definition of its
  own (`syn.of`, `obs.made`) lets the law say what it computes, the
  code unchanged in behaviour.
- **A recursive call needing its branch's fact**: where the induction
  hypothesis holds only in one case of a step's split (`x` not `y`),
  the step lemma takes it as a function of that case's equation, and
  the caller passes the recursion as that function (`final_k`).
- **A lemma wanting a mutually recursive partner** takes the partner's
  induction as a function argument (`sub_weak`'s `tl`), so that the
  recursion stays in one def (`sub_tail`).
- **Induct with the accumulator a definition has**: a list reversed
  onto an accumulator (`List.reverse.go(rest, q)`) steps by computation
  (`reverse.go(Con{x, r}, q)` is `reverse.go(r, Con{x, q})`), where the
  reversal of an append wants lemmas.
- **A rewrite is a local statement**: no `match` may follow it. Match
  first, then rewrite in each branch.
- **Text kept reversed, claimed by its last line**: where a writer
  builds its text backwards (`Tb`'s `acc`), state where things land by
  what lies from the text's last newline on (`from.nl`): text held
  within a line written after it leaves that the same (`onto_from`), a
  newline starts it over, and such equations chain by `Equal.trans`,
  with no arithmetic; the newlines counted follow from it
  (`nls_from`).
- **A second invariant along a proved walk**: where a law already
  follows a pass (`markers.items` its numbering), a law of another
  invariant over the same pass reuses its mirrors of the code's
  decisions and its layout, lemma for lemma (`inline.items`, 108
  lemmas written in a sitting); a pair's halves claimed by one `Bool`
  (`pil`) that a match on the pair reduces.
- **A mutation that runs the checker out of memory**: a mutation caught
  only inside a large proof term (a law joining others, its context
  written out) failed by exhausting the checker's memory, 3 GB in 37 s,
  rather than by a refutation; the part it breaks moved into a small
  lemma over a variable (`eown_il`) fails there, cleanly
  (`markers.inline`).
- **A walk naming the code's own states**: a law that follows a fold
  step by step (`wr.at`) calls the code's own step on the code's own
  state, and ends by comparing with the code's own result (its `fin`),
  so that a fault in how the steps compose is caught; checks on pieces
  computed apart from the code would pass it.
- **A bound on `U32.mod`**: the hub proves `U32.div` (`u32_div_to_nat`)
  but not `U32.mod`; its internal invariant gives it, the divmod's pair
  matched (`MU.internal_dm_go`, `mod10_lt`). A `%` rewrite by the hub's
  `internal_u32_add_exact` in a goal holding `U32.add(48, r)` overflowed
  the checker's stack; `Equal.trans` to a lemma rewriting a variable
  did not (`dig_ne`, `ne_k`).
- **A string literal splits by computation**: `codes("\nlaw ")` is
  `Con{10, codes("law ")}` to the checker, and a marker built by
  appending to such a literal is the newline before the literal's rest,
  with no lemma (`wh_put`).
- **A `U32` and its successor differ**, also past 2^32: through
  `to_nat` mod 2^32, split on `Nat.is_lt(1+n, m)`; below the modulus the
  sum is itself, else it is the modulus, its remainder 0, and `n` not 0
  (`u32_succ_ne`).
- **Templates prove as code does**: a proof def may take `~p`, and
  template parameters come first.
- **A traversal's effect on one projection**: where a writer threads
  a large state, state each step's effect on the one part the law
  reads (`cy`, a counter), for any state before it, so that steps
  chain by one rewrite (`keep`); an operation that leaves that part
  alone gets a lemma by matching the state alone, whatever else it
  is given (`tbput_any`).
- **U32 arithmetic**: through `U32.to_nat` and the hub's wrap laws
  (`u32_add_wrap`), its sums mod 2^32, the hub's `add_mod_left` and
  `mod_add_div` give associativity and commutativity (`u32_assoc`,
  `u32_comm`). A hypothesis of function type cannot be marked `+`:
  pass each instance needed as an equation of its own (`u32_assoc_n`).
- **Lemmas on the hub**: the package `0x8ae61ec3a6615abd35f196c07232ad28`
  (bend-mathlib) proves lists, `U32`, `Nat`, `Bool` and equality
  (`list.bend`, `u32.bend`, `nat.bend`, `bool.bend`, `equal.bend`).
  A fact of Bend's own types a proof needs and the hub lacks goes on
  [HubCandidates.md](HubCandidates.md), to offer upstream later.
- **Find a failing lemma by bisecting** the proof file into prefixes,
  each its own file, checked in turn: Bend reports the first failure, or
  only that its stack overflowed.
- **Check one law at a time**: Bend reports only the first failure,
  often of an earlier law a mutation breaks too, and a whole proof file
  is slow to recheck while one law is being written.
  `python3 -I scripts/one_law.py PROOF LAW` checks a copy cut to the law,
  its proof and the defs it reaches; with `--mutants FILE`, the copy
  unmutated and then each mutation naming the law, each expected to fail
  it, and where.
