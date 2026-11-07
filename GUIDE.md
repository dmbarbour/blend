# The Blend guide

Blend adds static objects to Bend. A `.blend` file is a Bend module that
may also hold objects; `blend` writes it out as a `.bend` file in which
the objects are gone. Everything inside a body is Bend, so read `bend
guide` first. Each example is one of Blend's samples, run as shown.

## A first module

```blend samples/override.blend
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

    $ blend override.blend
    hello, world / HELLO, world

`blend override.blend` writes `override.bend` beside it, then runs it.
For the objects, it writes:

    # blend: override.blend:4
    def Greeter.greet() -> String:
      "hello"

    # blend: override.blend:6
    def Greeter.show() -> String:
      Greeter.greet() ++ ", world"

    # blend: override.blend:10
    def Loud.greet() -> String:
      "HELLO"

    # blend: override.blend:6
    def Loud.show() -> String:
      Loud.greet() ++ ", world"

Each concrete object gets its own copy of every definition it has, its
calls bound to its own final definitions: `Loud.show` calls
`Loud.greet`. Nothing is shared between objects, so a definition with
one caller keeps one, and Bend folds each object's chain into one
compiled segment, as it does only while each function has a single
caller.

## Objects

```blend samples/prior.blend
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

- `object Name extends A, B with`, its members indented; no members, no
  `with`.
- `def f` introduces `f`; `upd def f`, or `upd f`, replaces the `f` it
  inherits. Introducing an inherited name, or updating a missing one, is
  an error.
- A bare name binds late, to the final definition of the concrete
  object written, so that an update reaches every definition calling
  it; a name the object lacks, to its hosts' (Nested objects), then the
  module's, then Bend's. `Obj.f` names `Obj`'s.
- `_f`, the prior, is the definition an update replaces: the next along
  the C3 linearization (`blend-c3`). `BoldLoud`'s is BoldLoud, Bold,
  Loud, Plain, so `Bold`'s `_tag` there is `Loud`'s: `*plain!*`.
- A local never shares a name with a definition a bare name could reach
  (`blend-no-shadowing`).

## Families

```blend samples/family.blend
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

A concrete object extending an abstract one is a family: it gets every
definition above it, bound to its own. Blend writes nothing for the
abstract object itself. It declares the hooks its definitions call,
`declare after`, and each family defines them; one that doesn't is an
error, unless it is abstract too. Each family defines one hook and gets
its own copy of every definition that calls it, where a template would
thread the hook through every signature.

## Sharing

```blend samples/sharing.blend
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

- A definition is affine by default: used in one place, so that Bend
  folds it into its caller; a second use is an error. A call to itself
  does not count.
- `shared`: one definition, which every use reaches.
- `copied`: a copy for each use, `Arith.inc.c1` and `Arith.inc.c2`,
  besides `Arith.inc` for plain Bend to call
  (`blend-copies-keep-their-name`); each copy brings copies of the
  affine definitions only it reaches.
- The module's own definitions are plain Bend, shared.

## Types and declarations

```blend samples/declares.blend
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

- A type is a member: `type S: Data = T`, or `type S = T` of kind Type.
  A name of one is a call, `S()`, bound like any definition, so no
  family threads type parameters. Datatypes stay the module's, plain
  Bend (the sample `types`).
- `declare type S: Data` asks each family for a type of that kind;
  `declare def push(...) -> S()`, or `declare empty() -> S()` dropping
  `def`, for a definition of that type, bound to the family's own `S`;
  Blend has Bend check each family's definition against its declaration
  (`blend-declares-witnessed`). `declare size` alone leaves the type to
  each family.

## Nested objects

```blend samples/nested.blend
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

Objects nest, written under their path, `Outer.Inner.path`. `^name`
steps out to the object a nested one sits in, its host; `^^name` two; a
top-level object's host is the module. A nested object is a member: a
child of `Outer` gets its own `Inner`, made again for it, whose `^` is
the child (`blend-frozen-host`). `extend Inner with` is `upd` for a
nested object, `extend abstract Inner` keeps it abstract; neither is
allowed at the top level. The samples `family-nested` and `nested-reach`
show them.

## Laws and proofs

```blend samples/monoid.blend
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

def main() -> IO(Unit):
  IO.print(Bool.show(AnyOf.op(True{}, AnyOf.zero())))
```

    $ blend monoid.blend
    True

A law is stated once; each concrete family gets its own instance,
`AnyOf.LAW.right_id`, bound to its own definitions, and Blend writes
it after the code, where Bend checks it. A program built carries none.

- `proof name(...)` proves a law where it is stated or in any object
  below; `upd proof` proves it again where a family needs its own. A
  concrete object must have a proof of every law it has; a law not yet
  proven lives only in an abstract object.
- Inside a proof, the law's own name is the proof itself, for induction;
  another law's name is that law's proof. A typed proof, `proof
  name(a: Nat, -b: Nat) -> {...}:`, is a lemma, with no law.
- A law is never updated, and code names no law or proof.
- The module's own laws, at its top level, are written `LAW.name`
  (`blend-laws-in-module`).

The samples `laws` and `laws-imported` show induction, lemmas, prior
proofs and laws across modules.

## Templates

Bend's templates pass through: a `~` argument is a reference like any,
bound to the final object's definition, or a closed lambda. A template
is affine like any definition: `shared`, Bend makes a copy for each
distinct set of `~` arguments; `copied`, a copy for each use
(`blend-templates-affine`; the sample `templates`).

## Imports

```blend samples/lib/shapes.blend
import Base

def twice(+n: U32) -> U32:
  (n * 2 : U32)

abstract object Shape with
  declare side
  def perimeter() -> U32:
    twice(twice(side()))

object Square extends Shape with
  def side() -> U32:
    3
```

```blend samples/imports.blend
import Base
import ./lib/shapes.blend as S

object Big extends S.Square with
  upd side() -> U32:
    (_side() * 10 : U32)

def main() -> IO(Unit):
  IO.print(U32.show(S.Square.perimeter()) ++ " " ++ U32.show(Big.perimeter()))
```

    $ blend imports.blend
    12 120

`import ./lib/shapes.blend as S` names the library's objects, `S.Square`,
to extend and to call; each module writes its own `.bend`, and imports
form no cycle. `Big`'s copies reach the library's definitions, datatypes
and imports through the alias, `S.twice`, or through one Blend reserves,
`Blend_1` (the sample `namespaces`; `blend-namespaces-as-bends`). An
import path is local, plain names led by `./` at most, never `../` or
`/`, so that a directory holds all it imports; or a package on Bend's
hub, its `.bend` files only for now (`blend-imports-local`).

## What Blend writes

- For each concrete object, every definition it has: the final `Obj.f`;
  a prior reached through `_f`, named for the object that wrote it,
  `BoldLoud.tag.Loud`; a copied one's copies, `Obj.f.c1`. Nothing for an
  abstract object.
- Every definition, called or not, so that a module is written once
  however many import it, and plain Bend can call `Loud.show`.
- The module's definitions, datatypes and imports as written
  (`blend-module-is-bend`).
- Callees first, as Bend requires.
- Before each definition, a marker naming its source, `# blend:
  FILE:LINE`; the lines below it follow the source from LINE.
- The laws, proofs and witnesses after the code.
- After the header, a stamp, `# blend stamp: VERSION HASH`: Blend's
  version stamp, which every change to Blend moves, and a hash of the
  module and every `.blend` it imports. A file whose stamp is what its sources give is current;
  `deps` reads the stamp, and `emit` leaves a current file as it is
  (`blend-stamps`).

## The command

    blend FILE.blend [args]   write the module and its imports, then run it
                              with bend; -o OUT, --check-only and --verdict
                              as bend's
    blend emit [--alone] [--force] [--no-check|--verdict] FILE.blend...
                              write each module's .bend and its imports'
                              beside them (--alone: only those named),
                              each current by its stamp left as it is
                              (--force: written all the same); then check
                              with bend those holding laws (--verdict: the
                              kernel's too)
    blend deps [--make] FILE.blend...
                              each module emit would write: current by its
                              stamp, stale, missing or refused; --make as
                              makefile rules
    blend show FILE.blend [--read|--objects|--resolve] [NAME]
                              the objects, a stage, or what NAME resolves to
    blend guide|version|rebuild|update|--help

`emit` writes nothing when any module named has errors. Blend's errors
take Bend's shape, and an error Bend reports on a written line is
followed by the line it comes from, `Source: FILE.blend:LINE`.

## Limits

- A definition may call itself; no two may call each other, as Bend has
  no mutual recursion (`blend-adds-no-bend-logic`).
- A module is known by its path made plain; reached through a symlink,
  it is two modules to Blend.
- Names beginning `Blend_`, and names with a part `LAW`, are Blend's.
- A path holding a newline is refused: it would break the lines naming
  it.
