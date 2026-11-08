# Written by Blend from operators.blend; do not edit.
# blend stamp: f6def9719dcd 512d9ffbfbe83e39
import Base

# blend: operators.blend:18
def Plain.add(+a: U32, +b: U32) -> U32:
  (a + b : U32)

# blend: operators.blend:20
def Plain.mul(+a: U32, +b: U32) -> U32:
  (a * b : U32)

# blend: operators.blend:22
def Plain.is_lt(+a: U32, +b: U32) -> Bool:
  (a < b : U32)

# blend: operators.blend:12
def Plain.poly(+x: U32) -> U32:
  (x * x + x : Plain)  # Plain.mul Plain.add

# blend: operators.blend:14
def Plain.less(+a: U32, +b: U32) -> Bool:
  (a < b : Plain)  # Plain.is_lt

# blend: operators.blend:26
def Mod7.add(+a: U32, +b: U32) -> U32:
  ((a + b : U32) % 7 : U32)

# blend: operators.blend:28
def Mod7.mul(+a: U32, +b: U32) -> U32:
  ((a * b : U32) % 7 : U32)

# blend: operators.blend:22
def Mod7.is_lt(+a: U32, +b: U32) -> Bool:
  (a < b : U32)

# blend: operators.blend:12
def Mod7.poly(+x: U32) -> U32:
  (x * x + x : Mod7)  # Mod7.mul Mod7.add

# blend: operators.blend:14
def Mod7.less(+a: U32, +b: U32) -> Bool:
  (a < b : Mod7)  # Mod7.is_lt

# blend: operators.blend:33
def Grid.Cell.add(+a: U32, +b: U32) -> U32:
  (a + b : U32)

# blend: operators.blend:35
def Grid.two(+a: U32) -> U32:
  (a + a : Grid.Cell)  # Grid.Cell.add

# blend: operators.blend:40
def Grid2.Cell.add(+a: U32, +b: U32) -> U32:
  (a + b + 100 : U32)

# blend: operators.blend:35
def Grid2.two(+a: U32) -> U32:
  (a + a : Grid2.Cell)  # Grid2.Cell.add

# blend: operators.blend:43
def main() -> IO(Unit):
  IO.print(U32.show(Plain.poly(5)) ++ " " ++ U32.show(Mod7.poly(5)) ++ " " ++ Bool.show(Mod7.less(2, 3)) ++ " " ++ U32.show(Grid.two(1)) ++ " " ++ U32.show(Grid2.two(1)))
