# Written by Blend from shapes.blend; do not edit.
# blend stamp: 6a79f2029262 3122fc3841d6fe94
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
