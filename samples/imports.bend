# Written by Blend from imports.blend; do not edit.
# blend stamp: 78e54ed99292 1d26aacb51e741fb
import Base
import ./lib/shapes.bend as S

# blend: lib/shapes.blend:12
def Big.side.Square() -> U32:
  3

# blend: imports.blend:5
def Big.side() -> U32:
  (Big.side.Square() * 10 : U32)

# blend: lib/shapes.blend:8
def Big.perimeter() -> U32:
  S.twice(S.twice(Big.side()))

# blend: imports.blend:8
def main() -> IO(Unit):
  IO.print(U32.show(S.Square.perimeter()) ++ " " ++ U32.show(Big.perimeter()))
