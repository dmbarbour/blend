# Written by Blend from nested-late.blend; do not edit.
# blend stamp: f6def9719dcd 8787c91c26499298
import Base

# blend: nested-late.blend:10
def Lib.v() -> U32:
  100

# blend: nested-late.blend:15
def Outer.Inner.k() -> U32:
  1

# blend: nested-late.blend:19
def Outer.Mid.Deep.k() -> U32:
  10

# blend: nested-late.blend:21
def Outer.f() -> U32:
  (Outer.Inner.k() + Outer.Mid.Deep.k() + Lib.v() : U32)

# blend: nested-late.blend:24
def Outer.Sub.g() -> U32:
  Outer.Inner.k()

# blend: nested-late.blend:29
def Outer2.Inner.k() -> U32:
  2

# blend: nested-late.blend:33
def Outer2.Mid.Deep.k() -> U32:
  20

# blend: nested-late.blend:21
def Outer2.f() -> U32:
  (Outer2.Inner.k() + Outer2.Mid.Deep.k() + Lib.v() : U32)

# blend: nested-late.blend:24
def Outer2.Sub.g() -> U32:
  Outer2.Inner.k()

# blend: nested-late.blend:44
def Square.Side.size() -> U32:
  3

# blend: nested-late.blend:39
def Square.area() -> U32:
  (Square.Side.size() * Square.Side.size() : U32)

# blend: nested-late.blend:47
def main() -> IO(Unit):
  IO.print(U32.show(Outer.f()) ++ " " ++ U32.show(Outer2.f()) ++ " " ++ U32.show(Outer.Sub.g()) ++ " " ++ U32.show(Outer2.Sub.g()) ++ " " ++ U32.show(Square.area()))
