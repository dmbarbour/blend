# Written by Blend from namespaces.blend; do not edit.
# blend stamp: 32dfe2de9450 de2b366a0cb0c85a
import Base
import ./lib/dims.bend as D
import ./lib/units.bend as Blend_1

# blend: lib/dims.blend:21
def Big.side.Square() -> U32:
  3

# blend: namespaces.blend:10
def Big.side() -> U32:
  (Big.side.Square() * 10 : U32)

# blend: lib/dims.blend:11
def Big.dims.of(+s: U32) -> D.Dim:
  D.Dim{s, s}

# blend: lib/dims.blend:13
def Big.area.of(d: D.Dim) -> U32:
  match d:
    case D.Dim{+w, +h}:
      Blend_1.cm2((w * h : U32))

# blend: lib/dims.blend:17
def Big.area() -> U32:
  Big.area.of(Big.dims.of(Big.side()))

# blend: namespaces.blend:13
def main() -> IO(Unit):
  IO.print(U32.show(D.Square.area()) ++ " " ++ U32.show(Big.area()))
