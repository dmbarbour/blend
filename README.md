# Blend

Static objects for Bend: inheritance, overrides and families, with
laws stated once for every family, written out as plain Bend in which
the objects are gone.

- **Extensible.** A new variant extends an object and overrides only
  what differs; everything it inherits is bound to its overrides. Code
  is reopened by extension, never edited in place.
- **Configurations that mix.** An object may extend several, each
  contributing its choices, combined in a fixed order (C3); `Bold` and
  `Loud` make `BoldLoud` without either knowing of the other.
- **Fast as written by hand.** Bend folds a chain of functions into one
  compiled segment only while each has a single caller; a helper two
  variants share has two, and a hook passed as a `~` argument threads
  every signature. Blend gives each object its own copy of every
  definition it inherits, so each variant folds on its own; sharing is
  asked for, never accidental.
- **Laws per family.** A law stated once in an abstract object is
  instantiated, and proved, for each concrete family, and Bend checks
  it.

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

`Counted.run` calls `Counted.step`, which calls `Counted.after`: no
template argument, no shared caller.

## Getting started

Blend needs Bend (`curl -fsSL https://bend-lang.com/install.sh | sh`),
and clang to build itself natively; without clang it runs through Bend,
slower. Releases are planned; for now, from a checkout:

    git clone https://github.com/dmbarbour/blend
    sh blend/install.sh

That puts `blend` beside `bend`, in `~/.bend/bin`. Then, in
`blend/samples/`:

    blend family.blend        write family.bend, then run it with bend
    blend emit monoid.blend   write monoid.bend, and have bend check its laws
    blend guide               the language, what Blend writes, the command
                              (GUIDE.md)
    blend --help

## Working on Blend

Blend is written in Bend (`blend.bend`), and holds itself to laws it
proves (`LAWS.bend`, `PROOF.bend`). `samples/` is its specification:
each `.blend` beside what it writes and prints, or the error it must
raise; the guide's examples are among them. `check.sh` is the gate;
`AGENTS.md` has the rest, and `docs/plans/` what comes next.
