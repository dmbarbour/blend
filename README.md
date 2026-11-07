# Blend

Static objects for Bend: inheritance, overrides and families, with
laws stated once for every family, written out as plain Bend in which
the objects are gone.

Bend compiles a chain of functions into one fast segment only while
each function has a single caller. Code meant to vary resists that: a
hook passed as a template argument threads through every signature on
its way down, and a helper two variants share has two callers. Blend
gives each object its own copy of every definition it inherits, bound
to its own overrides, so each variant folds on its own; sharing is
asked for, never accidental.

```blend machine.blend
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

`blend machine.blend` prints `8 15`. It wrote `machine.bend`, where
`Counted.run` calls `Counted.step`, which calls `Counted.after`: no
template argument, no shared caller.

## Getting started

Blend needs Bend (`curl -fsSL https://bend-lang.com/install.sh | sh`),
and clang to build itself natively; without clang it runs through Bend,
slower. Releases are planned; for now, from a checkout:

    git clone https://github.com/dmbarbour/blend
    sh blend/install.sh

That puts `blend` beside `bend`, in `~/.bend/bin`. Then:

    blend machine.blend        write machine.bend, then run it with bend
    blend emit machine.blend   write it, and have bend check its laws
    blend guide                the language, what Blend writes, the command
    blend --help

Errors come in Bend's shape, and an error Bend reports on a written line
is followed by the `.blend` line it comes from.

## Working on Blend

Blend is written in Bend (`blend.bend`), and holds itself to laws it
proves (`LAWS.bend`, `PROOF.bend`). `samples/` is its specification:
each `.blend` beside what it writes and prints, or the error it must
raise. `check.sh` is the gate; `AGENTS.md` has the rest, and
`docs/plans/` what comes next.
