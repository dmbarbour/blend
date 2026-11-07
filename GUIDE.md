# The Blend guide

Blend adds static objects to Bend. A `.blend` file is a Bend module that
may also hold objects; `blend` writes it out as a `.bend` file in which
the objects are gone, each object's definitions copied out under its
name. Everything inside a body is Bend: read `bend guide` first.

## A first module

```blend greet.blend
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

`blend greet.blend` writes `greet.bend` beside it and runs it, printing
`hello, world / HELLO, world`. What it writes, its header and `main`
aside:

    # blend: greet.blend:4
    def Greeter.greet() -> String:
      "hello"

    # blend: greet.blend:6
    def Greeter.show() -> String:
      Greeter.greet() ++ ", world"

    # blend: greet.blend:10
    def Loud.greet() -> String:
      "HELLO"

    # blend: greet.blend:6
    def Loud.show() -> String:
      Loud.greet() ++ ", world"

Each object gets its own copy of every definition it has, its calls
bound to its own: `Loud.show` calls `Loud.greet`. No copy is shared
between objects, so a definition called once stays called once, and
Bend folds each object's chain into one compiled segment: a family of
variants, each compiled as if written by hand.

## Objects

- `object Name extends A, B with`, its members indented; an object with
  no members leaves out `with`.
- `def f` introduces `f`; `upd def f`, or `upd f`, replaces the `f` it
  inherits. Introducing a name already inherited, or updating one that
  isn't, is an error.
- A bare name in a body binds to the final object's definition, so an
  update reaches every definition that calls it. `Obj.f` names that
  object's.
- `_f` is the definition an update replaces: the next object's in the C3
  linearization (`blend-c3`). A parent named twice is one parent.
- A bare name no object in reach defines is the module's, or Bend's. A
  local never shares a name with a definition in reach
  (`blend-no-shadowing`).

```blend prior.blend
import Base

object Plain with
  def tag() -> String:
    "plain"

object Bold extends Plain with
  upd tag() -> String:
    "*" ++ _tag() ++ "*"

object Loud extends Plain with
  upd tag() -> String:
    _tag() ++ "!"

object BoldLoud extends Bold, Loud

def main() -> IO(Unit):
  IO.print(BoldLoud.tag())
```

BoldLoud linearizes as BoldLoud, Bold, Loud, Plain, and prints
`*plain!*`.

## Families

An abstract object is emitted only through its children. It declares
the hooks its definitions call; each concrete child gives them. Where a
template would thread a hook through every signature, a family overrides
one definition.

```blend family.blend
import Base

abstract object Machine with
  declare after
  def step(+n: U32) -> U32:
    after((n * 2 : U32))

object Plain extends Machine with
  def after(+n: U32) -> U32:
    n

object Counted extends Machine with
  def after(+n: U32) -> U32:
    (n + 1 : U32)

def main() -> IO(Unit):
  IO.print(U32.show(Plain.step(1)) ++ " " ++ U32.show(Counted.step(1)))
```

A concrete object that leaves a declared name undefined is an error;
mark it `abstract` to leave it to its children.

## Sharing

Each definition says how its uses share it:

- affine, the default: one use at most, so that Bend folds it into its
  caller. A second use is an error, naming the uses.
- `shared def`: one copy, however many use it.
- `copied def`: a copy for each use, `Obj.f.c1`, `Obj.f.c2`, each folding
  into its own caller, besides `Obj.f` itself for plain Bend to call
  (`blend-copies-keep-their-name`). An affine definition only a copy
  reaches is copied with it.

```blend sharing.blend
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

A definition calling itself is one use. The module's own definitions are
Bend's, shared.

## Types and declarations

Types are members: `type S = T` is a shared definition returning a type,
`type S: Data = T` one of kind Data, and a name of one is a call, `S()`,
bound like any other, so no family threads type parameters. `declare
type S: Data` asks each family for one.

A typed declaration says what a family's definition must be, bound to
the family's own types: `declare def push(st: S(), +x: U32) -> S()`, or
`declare push(...)` for short. Blend has no type checker of its own: for
each concrete object it writes a witness that Bend checks
(`blend-declares-witnessed`).

```blend stack.blend
import Base

abstract object Stack with
  declare type S: Data
  declare def push(st: S(), +x: U32) -> S()
  declare empty() -> S()
  def one(+x: U32) -> S():
    push(empty(), x)

object Listed extends Stack with
  type S: Data = List<&2, U32>
  def empty() -> S():
    Nil{}
  def push(st: S(), +x: U32) -> S():
    Con{x, st}

object Summed extends Stack with
  type S: Data = U32
  def empty() -> S():
    0
  def push(+st: S(), +x: U32) -> S():
    (st + x : U32)
```

Datatypes stay the module's, plain Bend; a type member can be one's
argument, `Box<S()>`.

## Nested objects

Objects nest, emitted under their path, `Outer.Inner.f`. `^name` steps
out of the innermost object to its host's scope, `^^name` two; a
top-level object's host is the module.

```blend nested.blend
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

A nested object is a member: a child of `Outer` has its own `Inner`,
made again for it, its `^` the child (`blend-frozen-host`). `extend Inner
with` updates an inherited one, `extend abstract Inner` keeps it
abstract; `extend` stays out of the top level. The samples
`family-nested` and `nested-reach` show the rest.

## Laws and proofs

A law is a member: a claim over the object's definitions, Bend's, each
concrete object getting its own instance. `proof name(...)` proves it
where it is stated or in any object below; `upd proof` proves it again
where a family needs its own. A concrete object proves every law it has;
a law not yet proven belongs in an abstract object.

```blend laws.blend
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
```

The law is written `law AnyOf.LAW.right_id:` and its proof
`def AnyOf.LAW.right_id(x):`, after the module's code
(`blend-laws-in-module`). Bend checks them whenever it loads the file;
a program built carries none, since Bend compiles what `main` reaches.

- A typed proof, `proof add_succ(a: Nat, -b: Nat) -> {...}:`, is a
  lemma. Inside a proof, its own law names the proof itself, for
  induction; another law names that law's proof.
- A law is stated once, never updated, and code names no law, proof or
  lemma. Names with a part `LAW` are Blend's.
- The module's own laws, at its top level, are written `LAW.name`.

The samples `laws` and `laws-imported` show induction, lemmas, priors
and laws across modules.

## Templates

Bend's templates pass through: a `~` argument is a reference like any,
bound to the final object's definition, or a closed lambda. A template
is affine like any definition: mark it `shared`, Bend making a copy for
each distinct set of `~` arguments, or `copied`, a copy for each use
(`blend-templates-affine`; the sample `templates`).

## Imports

`import ./lib/shapes.blend as S` names that module's objects `S.Square`,
to extend and to call. A path is local, plain names led by `./` at
most, never `../` or `/`, so that a directory holds all it imports; or a
package's on Bend's hub, its `.bend` files only for now
(`blend-imports-local`). Each module writes its own `.bend`, and imports
form no cycle.

```blend lib/shapes.blend
import Base

abstract object Shape with
  declare side
  def perimeter() -> U32:
    (side() * 4 : U32)

object Square extends Shape with
  def side() -> U32:
    3
```

```blend shapes.blend
import Base
import ./lib/shapes.blend as S

object Big extends S.Square with
  upd side() -> U32:
    (_side() * 10 : U32)

def main() -> IO(Unit):
  IO.print(U32.show(S.Square.perimeter()) ++ " " ++ U32.show(Big.perimeter()))
```

`Big` copies what it inherits; the copies name the library's own
definitions and datatypes through the importer's alias for it, or one
Blend reserves, `Blend_1` (`blend-namespaces-as-bends`).

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
