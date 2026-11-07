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
For the objects it writes:

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

Each object gets its own copy of every definition it has, bound to its
own: `Loud.show` calls `Loud.greet`. Nothing is shared between objects,
so a definition called once stays called once, and Bend folds each
object's chain into one compiled segment.

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
- A bare name binds to the final object's definition; `Obj.f` names that
  object's.
- `_f` is the definition an update replaces: the next in the C3
  linearization (`blend-c3`), here BoldLoud, Bold, Loud, Plain.
- A bare name no object in reach defines is the module's, or Bend's. A
  local never shares a name with a definition in reach
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

An abstract object is written only through its children. It declares
the hooks its definitions call, and each concrete child defines them;
one that doesn't is an error, unless it is abstract too. Where a
template would pass the hook down through every signature, each family
overrides one definition, and gets its own copy of every definition that
calls it. A definition may call itself.

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

- Affine, the default: one use, so that Bend folds it into its caller;
  a second is an error.
- `shared`: one copy for every use.
- `copied`: a copy for each use, `Arith.inc.c1` and `Arith.inc.c2`,
  besides `Arith.inc` for plain Bend to call
  (`blend-copies-keep-their-name`); an affine definition only a copy
  reaches is copied with it.
- A definition's calls to itself are no use, and the module's own
  definitions are Bend's, shared.

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
  `declare def push(...) -> S()`, or `declare empty() -> S()` for short,
  for a definition of that type, bound to the family's own `S`. Blend
  writes a witness for each concrete object, which Bend checks
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
steps out to the host's scope, `^^name` two; a top-level object's host
is the module. A nested object is a member: a child of `Outer` gets its
own `Inner`, made again for it, its `^` the child (`blend-frozen-host`).
`extend Inner with` updates an inherited one, `extend abstract Inner`
keeps it abstract; `extend` stays out of the top level. The samples
`family-nested` and `nested-reach` show more.

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
  concrete object proves every law it has; a law not yet proven belongs
  in an abstract object.
- A typed proof, `proof add_succ(a: Nat, -b: Nat) -> {...}:`, is a
  lemma. In a proof, its own law names the proof itself, for induction;
  another law names that law's proof.
- A law is never updated, and code names no law, proof or lemma.
- The module's own laws, at its top level, are written `LAW.name`
  (`blend-laws-in-module`).

The samples `laws` and `laws-imported` show induction, lemmas, priors
and laws across modules.

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
form no cycle. `Big`'s copies name the library's definitions through the
alias, `S.twice`; its datatypes and its own imports too, or through an
alias Blend reserves, `Blend_1` (the sample `namespaces`;
`blend-namespaces-as-bends`). A path is local, plain names led by `./`
at most, never `../` or `/`, so that a directory holds all it imports;
or a package's on Bend's hub, its `.bend` files only for now
(`blend-imports-local`).

## What Blend writes

- For each concrete object, every definition it has: the final `Obj.f`;
  a replaced one reached through `_f`, `Obj.f.Origin`; a copied one's
  copies, `Obj.f.c1`. An abstract object writes nothing of its own.
- Every definition, called or not, so that a module is written once
  however many import it, and plain Bend can call `Loud.show`.
- The module's definitions, datatypes and imports as written
  (`blend-module-is-bend`).
- Callees first, as Bend requires (`blend-adds-no-bend-logic`).
- Before each definition, a marker naming where it is written, `# blend:
  FILE:LINE`; the lines below it follow the source from LINE.
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

- No two definitions may call each other: Bend has no mutual recursion.
- A module is known by its path made plain; reached through a symlink,
  it is two modules to Blend.
- Names beginning `Blend_`, and names with a part `LAW`, are Blend's.
- A path holding a newline is refused: it would break the lines naming
  it.
