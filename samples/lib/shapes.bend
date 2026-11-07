# Written by Blend from shapes.blend; do not edit.
# blend stamp: 3efd9b0ef5dd 34efbe9f18a6c499
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
