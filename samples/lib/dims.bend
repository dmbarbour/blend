# Written by Blend from dims.blend; do not edit.
# blend stamp: eec4e8aaf12a dc7eed85d0f4e91d
import Base
import ./units.bend as U

# blend: dims.blend:6
type Dim is Data:
  Dim{+w: U32, +h: U32}

# blend: dims.blend:21
def Square.side() -> U32:
  3

# blend: dims.blend:11
def Square.dims.of(+s: U32) -> Dim:
  Dim{s, s}

# blend: dims.blend:13
def Square.area.of(d: Dim) -> U32:
  match d:
    case Dim{+w, +h}:
      U.cm2((w * h : U32))

# blend: dims.blend:17
def Square.area() -> U32:
  Square.area.of(Square.dims.of(Square.side()))
