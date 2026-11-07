# Written by Blend from templates.blend; do not edit.
# blend stamp: 3428828f8605 606fa21c5c0225c8
import Base

# blend: templates.blend:23
def Twice.apply(~f: U32 -> U32, x: U32) -> U32:
  f(f(x))

# blend: templates.blend:25
def Twice.count(-A: Data, xs: List<&2, A>) -> U32:
  U32.from_nat(List.length(&2, A, xs))

# blend: templates.blend:15
def Twice.inc(x: U32) -> U32:
  (x + 1 : U32)

# blend: templates.blend:17
def Twice.bumped(x: U32) -> U32:
  Twice.apply(~Twice.inc, x)

# blend: templates.blend:19
def Twice.doubled(x: U32) -> U32:
  Twice.apply(~(y => (y * 2 : U32)), x)

# blend: templates.blend:28
def main() -> IO(Unit):
  IO.print(U32.show(Twice.bumped(1)) ++ " " ++ U32.show(Twice.doubled(1)) ++ " " ++ U32.show(Twice.count(U32, [7, 8])))

# blend: templates.blend:13
def Twice.LAW.apply.as_declared(~f: U32 -> U32, x: U32) -> U32: Twice.apply(~f, x)

# blend: templates.blend:14
def Twice.LAW.count.as_declared(-A: Data, xs: List<&2, A>) -> U32: Twice.count(A, xs)
