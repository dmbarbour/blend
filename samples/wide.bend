# Written by Blend from wide.blend; do not edit.
# blend stamp: 763442a0527c f492003a51af9dd8
import Base
import ./lib/wide.bend as L

# blend: wide.blend:9
def Narrow.base(+x: U32) -> U32:
  x

# blend: lib/wide.blend:7
def Narrow.w1(+x: U32) -> U32:
  (Narrow.base(x) + 1 : U32)

# blend: lib/wide.blend:9
def Narrow.w2(+x: U32) -> U32:
  (Narrow.w1(x) + 1 : U32)

# blend: lib/wide.blend:11
def Narrow.w3(+x: U32) -> U32:
  (Narrow.w2(x) + 1 : U32)

# blend: lib/wide.blend:13
def Narrow.w4(+x: U32) -> U32:
  (Narrow.w3(x) + 1 : U32)

# blend: lib/wide.blend:15
def Narrow.w5(+x: U32) -> U32:
  (Narrow.w4(x) + 1 : U32)

# blend: lib/wide.blend:17
def Narrow.w6(+x: U32) -> U32:
  (Narrow.w5(x) + 1 : U32)

# blend: lib/wide.blend:19
def Narrow.w7(+x: U32) -> U32:
  (Narrow.w6(x) + 1 : U32)

# blend: lib/wide.blend:21
def Narrow.w8(+x: U32) -> U32:
  (Narrow.w7(x) + 1 : U32)

# blend: wide.blend:12
def main() -> IO(Unit):
  IO.print(U32.show(Narrow.w8(0)))
