# The Blend guide

Blend adds static objects to Bend. A `.blend` file is a Bend module that
may also hold objects; `blend` writes it out as a `.bend` file in which
the objects are gone, each object's definitions copied out under its
name. Everything inside a body is Bend: read `bend guide` first. Each
example here is one of Blend's samples, in `samples/`, beside what Blend
writes for it.

## A first module

```blend samples/override.blend
# Introductions, overrides and late binding: a bare name binds to the
# final object's definition, so Loud's show calls Loud's greet.
import Base

object Greeter with
  def greet() -> String:
    "hello"
  def show() -> String:
    greet() ++ ", world"

object Loud extends Greeter with
  upd greet() -> String:
    "HELLO"

def main() -> IO(Unit):
  IO.print(Greeter.show() ++ " / " ++ Loud.show())
```

`blend override.blend` writes `override.bend` beside it, then runs it:

    $ blend override.blend
    hello, world / HELLO, world

What it writes, its header and `main` aside:

    # blend: override.blend:6
    def Greeter.greet() -> String:
      "hello"

    # blend: override.blend:8
    def Greeter.show() -> String:
      Greeter.greet() ++ ", world"

    # blend: override.blend:12
    def Loud.greet() -> String:
      "HELLO"

    # blend: override.blend:8
    def Loud.show() -> String:
      Loud.greet() ++ ", world"

Each object gets its own copy of every definition it has, its calls
bound to its own. No copy is shared between objects, so a definition
called once stays called once, and Bend folds each object's chain into
one compiled segment: a family of variants, each compiled as if written
by hand.

## Objects

- `object Name extends A, B with`, its members indented; an object with
  no members leaves out `with`.
- `def f` introduces `f`; `upd def f`, or `upd f`, replaces the `f` it
  inherits. Introducing a name already inherited, or updating one that
  isn't, is an error.
- A bare name in a body binds to the final object's definition; `Obj.f`
  names that object's.
- `_f` is the definition an update replaces: the next object's in the C3
  linearization (`blend-c3`). A parent named twice is one parent.
- A bare name no object in reach defines is the module's, or Bend's. A
  local never shares a name with a definition in reach
  (`blend-no-shadowing`).

```blend samples/prior.blend
# Priors and multiple inheritance: `_tag` is the definition an update
# replaces (`upd def`, or `upd` alone, its sugar), the next in the C3
# linearization. BoldLoud linearizes as BoldLoud, Bold, Loud, Plain, so
# its tag is Bold's, whose prior is Loud's, whose prior is Plain's.
import Base

object Plain with
  def tag() -> String:
    "plain"

object Bold extends Plain with
  upd def tag() -> String:
    "*" ++ _tag() ++ "*"

object Loud extends Plain with
  upd tag() -> String:
    _tag() ++ "!"

object BoldLoud extends Bold, Loud

def main() -> IO(Unit):
  IO.print(Plain.tag() ++ " " ++ Bold.tag() ++ " " ++ Loud.tag() ++ " " ++ BoldLoud.tag())
```

    $ blend prior.blend
    plain *plain* plain! *plain!*

## Families

An abstract object is written only through its children. It declares
the hooks its definitions call; each concrete child gives them, or is an
error unless marked `abstract` too.

```blend samples/family.blend
# Families as objects: an abstract object declares the hook its
# definitions call, and each family introduces it. Where a template took
# the hook as a `~` argument through every signature, a family overrides
# one definition, and gets its own copy of every definition that calls
# it. A definition may call itself; Bend checks that it terminates.
import Base

abstract object Machine with
  declare after
  def step(+n: U32) -> U32:
    after((n * 2 : U32))
  def run(k: Nat, +n: U32) -> U32:
    match k:
      case 0n:
        n
      case 1n+p:
        run(p, step(n))

object Plain extends Machine with
  def after(+n: U32) -> U32:
    n

object Counted extends Machine with
  def after(+n: U32) -> U32:
    (n + 1 : U32)

def main() -> IO(Unit):
  IO.print(U32.show(Plain.run(3n, 1)) ++ " " ++ U32.show(Counted.run(3n, 1)))
```

    $ blend family.blend
    8 15

## Sharing

- affine, the default: one use at most, so that Bend folds it into its
  caller; a second use is an error, naming the uses.
- `shared def`: one copy, however many use it.
- `copied def`: a copy for each use, `Obj.f.c1`, `Obj.f.c2`, besides
  `Obj.f` for plain Bend to call (`blend-copies-keep-their-name`); an
  affine definition only a copy reaches is copied with it.

```blend samples/sharing.blend
# Sharing, stated per definition: affine by default, one use in the
# emitted program, so that Bend folds it into its caller; `shared`, one
# copy however many use it; `copied`, a copy for each use, each folding
# into its own caller, besides the copy by its own name, for a plain
# `.bend` file to call. Here inc is copied for its two uses in twice, and
# show is shared by its two uses in report.
import Base

object Arith with
  copied def inc(+n: U32) -> U32:
    (n + 1 : U32)
  shared def show(+n: U32) -> String:
    U32.show(n)
  def twice(+n: U32) -> U32:
    inc(inc(n))
  def report(+n: U32) -> String:
    show(n) ++ " -> " ++ show(twice(n))

def main() -> IO(Unit):
  IO.print(Arith.report(5))
```

    $ blend sharing.blend
    5 -> 7

The module's own definitions are Bend's, shared.

## Types and declarations

A type is a member, and a name of one a call, `S()`, bound like any
other, so no family threads type parameters; datatypes stay the
module's, plain Bend (the sample `types`). A typed declaration says what
a family's definition must be, bound to the family's own types; Blend
writes a witness for each concrete object, which Bend checks
(`blend-declares-witnessed`).

```blend samples/declares.blend
# Typed declarations: an abstract object says what a definition its
# families give must be, `declare def push(st: S(), +x: U32) -> S()`, or
# `declare empty() -> S()` for short, and of what kind a type must be,
# `declare type S: Data`. Each family's definitions are checked against
# the declaration bound to the family's own types, by witnesses Blend
# writes into declares.bend with the laws, which Bend checks and the
# program never calls. `declare size` stays untyped, each family's its own.
import Base

abstract object Stack with
  declare type S: Data
  declare def push(st: S(), +x: U32) -> S()
  declare empty() -> S()
  declare size
  def one(+x: U32) -> S():
    push(empty(), x)

object Listed extends Stack with
  type S: Data = List<&2, U32>
  def empty() -> S():
    Nil{}
  def push(st: S(), +x: U32) -> S():
    Con{x, st}
  def size(st: S()) -> U32:
    U32.from_nat(List.length(&2, U32, st))

object Counted extends Stack with
  type S: Data = U32
  def empty() -> S():
    0
  def push(+st: S(), +x: U32) -> S():
    (st + x : U32)
  def size(+st: S()) -> U32:
    st

def main() -> IO(Unit):
  IO.print(U32.show(Listed.size(Listed.one(5))) ++ " " ++ U32.show(Counted.size(Counted.one(5))))
```

    $ blend declares.blend
    1 5

## Nested objects

```blend samples/nested.blend
# The module is no object: its definitions are Bend's, emitted as they
# are. Objects nest, each emitted with its path as a prefix. `^name`
# steps out of the innermost object to its host's scope, as in glam,
# `^^name` two steps; a top-level object's host is the module.
import Base

def unit() -> String:
  "m"

object Outer with
  def name() -> String:
    "outer"
  object Inner with
    def name() -> String:
      "inner"
    def path() -> String:
      ^name() ++ "." ++ name() ++ "." ++ ^^unit()

def main() -> IO(Unit):
  IO.print(Outer.Inner.path())
```

    $ blend nested.blend
    outer.inner.m

A nested object is a member: a child of `Outer` has its own `Inner`,
made again for it, its `^` the child (`blend-frozen-host`). `extend Inner
with` updates an inherited one, `extend abstract Inner` keeps it
abstract; `extend` stays out of the top level. The samples
`family-nested` and `nested-reach` show the rest.

## Laws and proofs

```blend samples/monoid.blend
# Laws: an abstract object states a law over what its families give, and
# each concrete family gets its own instance, bound to its own
# definitions, and proves it, here by cases. Blend writes the laws and
# their proofs after the code, `AnyOf.LAW.right_id`, where Bend checks
# them; the program carries none.
import Base

abstract object Monoid with
  declare type T
  declare zero, op
  law right_id:
    for +x: T()
    {op(x, zero()) == x : T()}

object AnyOf extends Monoid with
  type T: Data = Bool
  def zero() -> T():
    False{}
  def op(+a: T(), +b: T()) -> T():
    a || b
  proof right_id(x):
    match x:
      case True{}:
        {==}
      case False{}:
        {==}

object AllOf extends Monoid with
  type T: Data = Bool
  def zero() -> T():
    True{}
  def op(+a: T(), +b: T()) -> T():
    a && b
  proof right_id(x):
    match x:
      case True{}:
        {==}
      case False{}:
        {==}

def main() -> IO(Unit):
  IO.print(Bool.show(AnyOf.op(True{}, AnyOf.zero())) ++ " " ++ Bool.show(AllOf.op(True{}, AllOf.zero())))
```

    $ blend monoid.blend
    True True

- `proof name(...)` proves a law where it is stated or in any object
  below; `upd proof` proves it again where a family needs its own. A
  concrete object proves every law it has; a law not yet proven belongs
  in an abstract object.
- A typed proof, `proof add_succ(a: Nat, -b: Nat) -> {...}:`, is a
  lemma. Inside a proof, its own law names the proof itself, for
  induction; another law names that law's proof.
- A law is stated once, never updated, and code names no law, proof or
  lemma. Names with a part `LAW` are Blend's.
- The module's own laws, at its top level, are written `LAW.name`
  (`blend-laws-in-module`).

The samples `laws` and `laws-imported` show induction, lemmas, priors
and laws across modules.

## Templates

Bend's templates pass through: a `~` argument is a reference like any,
bound to the final object's definition, or a closed lambda. A template
is affine like any definition: mark it `shared`, Bend making a copy for
each distinct set of `~` arguments, or `copied`, a copy for each use
(`blend-templates-affine`; the sample `templates`).

## Imports

A path is local, plain names led by `./` at most, never `../` or `/`,
so that a directory holds all it imports; or a package's on Bend's hub,
its `.bend` files only for now (`blend-imports-local`). Each module
writes its own `.bend`, and imports form no cycle.

```blend samples/lib/shapes.blend
# A library the sample `imports` imports: a module emits its own `.bend`
# (`lib/shapes.bend`), and a module extending its objects copies what it
# inherits, its names kept: its datatypes and its imports, named in the
# copy through the importer's own alias for the file, else one Blend
# reserves (`Blend_1`).
import Base
import ./units.bend as U

type Dim is Data:
  Dim{+w: U32, +h: U32}

def twice(+n: U32) -> U32:
  (n * 2 : U32)

abstract object Shape with
  declare side
  def perimeter() -> U32:
    twice(twice(side()))
  def dims.of(+s: U32) -> Dim:
    Dim{s, s}
  def area.of(d: Dim) -> U32:
    match d:
      case Dim{+w, +h}:
        U.cm2((w * h : U32))
  def area() -> U32:
    area.of(dims.of(side()))

object Square extends Shape with
  shared def side() -> U32:
    3
```

```blend samples/imports.blend
# Imports: `import ./lib/shapes.blend as S` names the library's objects
# `S.Square`, to extend and to call. Each module emits its own `.bend`,
# this one importing the library's; an object extending one of its
# objects copies what it inherits, the library's own definitions named
# through the alias, and an object means the same however an import
# reaches it.
import Base
import ./lib/shapes.blend as S

object Big extends S.Square with
  shared upd side() -> U32:
    (_side() * 10 : U32)

def main() -> IO(Unit):
  IO.print(U32.show(S.Square.perimeter()) ++ " " ++ U32.show(Big.perimeter()) ++ " " ++ U32.show(Big.area()))
```

    $ blend imports.blend
    12 120 90000

## What Blend writes

- For each concrete object, every definition it has, its own copy: the
  final `Obj.f`; a replaced one reached by `_f`, `Obj.f.Origin`; a
  copied one's copies, `Obj.f.c1`. An abstract object writes nothing of
  its own.
- Every definition, whether or not anything calls it, so a module is
  written once however many import it, and plain Bend may call
  `Loud.show` by name.
- The module's definitions, datatypes and imports as written
  (`blend-module-is-bend`).
- Callees first, as Bend requires. Two definitions calling each other
  are an error, as Bend has no mutual recursion
  (`blend-adds-no-bend-logic`).
- Before each definition a marker, `# blend: FILE:LINE`; the lines
  after it are the source's lines after LINE.
- The laws, proofs and witnesses after the code.

## The command

    blend FILE.blend [args]   emit the module's tree, then run it with bend;
                              -o OUT, --check-only and --verdict as bend's
    blend emit [--alone] [--no-check|--verdict] FILE.blend...
                              write each module's .bend and its imports'
                              beside them; then check with bend those
                              holding laws (--verdict: the kernel's too)
    blend deps [--make] FILE.blend...
                              each module emit would write: current, stale,
                              missing or refused; --make as makefile rules
    blend show FILE.blend [--read|--objects|--resolve] [NAME]
                              the objects, a stage, or what NAME resolves to
    blend guide|version|rebuild|update|--help

`emit` writes nothing when any module named has errors. Blend's errors
take Bend's shape, and an error Bend reports on a written line is
followed by the line it comes from, `Source: FILE.blend:LINE`.

## Limits

- No mutual recursion: Bend has none.
- A module is known by its path made plain; reached through a symlink,
  it is two modules to Blend.
- Names beginning `Blend_`, and names with a part `LAW`, are Blend's.
- A path holding a newline is refused: it would break the lines naming
  it.
