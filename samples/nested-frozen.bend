# Written by Blend from nested-frozen.blend; do not edit.
# blend stamp: 763442a0527c decfdd635f66c027
import Base

# blend: nested-frozen.blend:9
def Tag.t() -> U32:
  7

# blend: nested-frozen.blend:14
def Outer.Tag.t() -> U32:
  5

# blend: nested-frozen.blend:17
def Outer.Inner.u() -> U32:
  Outer.Tag.t()

# blend: nested-frozen.blend:22
def Outer2.Tag.t() -> U32:
  6

# blend: nested-frozen.blend:17
def Outer2.Inner.u() -> U32:
  Outer2.Tag.t()

# blend: nested-frozen.blend:17
def Y.u() -> U32:
  Outer2.Tag.t()

# blend: nested-frozen.blend:27
def main() -> IO(Unit):
  IO.print(U32.show(Outer.Inner.u()) ++ " " ++ U32.show(Outer2.Inner.u()) ++ " " ++ U32.show(Y.u()) ++ " " ++ U32.show(Tag.t()))
