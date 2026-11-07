# Written by Blend from family.blend; do not edit.
# blend stamp: 93f00e14ee3f 254d595871b0794e
import Base

# blend: family.blend:15
def Plain.after(+n: U32) -> U32:
  n

# blend: family.blend:5
def Plain.step(+n: U32) -> U32:
  Plain.after((n * 2 : U32))

# blend: family.blend:7
def Plain.run(k: Nat, +n: U32) -> U32:
  match k:
    case 0n:
      n
    case 1n+p:
      Plain.run(p, Plain.step(n))

# blend: family.blend:19
def Counted.after(+n: U32) -> U32:
  (n + 1 : U32)

# blend: family.blend:5
def Counted.step(+n: U32) -> U32:
  Counted.after((n * 2 : U32))

# blend: family.blend:7
def Counted.run(k: Nat, +n: U32) -> U32:
  match k:
    case 0n:
      n
    case 1n+p:
      Counted.run(p, Counted.step(n))

# blend: family.blend:22
def main() -> IO(Unit):
  IO.print(U32.show(Plain.run(3n, 1)) ++ " " ++ U32.show(Counted.run(3n, 1)))
