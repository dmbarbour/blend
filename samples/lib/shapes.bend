# Written by Blend from shapes.blend; do not edit.
# blend stamp: cfe7d563de05 6d5eb2713564a157
import Base

# blend: shapes.blend:3
def twice(+n: U32) -> U32:
  (n * 2 : U32)

# blend: shapes.blend:12
def Square.side() -> U32:
  3

# blend: shapes.blend:8
def Square.perimeter() -> U32:
  twice(twice(Square.side()))
