# Written by Blend from laws-imported.blend; do not edit.
# blend stamp: 1 71f1c74fed62d573
import Base
import ./lib/adds.bend as A

# blend: laws-imported.blend:10
def Zero.zero() -> Nat:
  0n

# blend: lib/adds.blend:8
def Zero.plus(+a: Nat, +b: Nat) -> Nat:
  Nat.add(a, b)

# blend: laws-imported.blend:20
def Again.zero() -> Nat:
  0n

# blend: lib/adds.blend:8
def Again.plus(+a: Nat, +b: Nat) -> Nat:
  Nat.add(a, b)

# blend: laws-imported.blend:25
def main() -> IO(Unit):
  IO.print(Nat.show(Zero.plus(2n, Again.plus(1n, Zero.zero()))))

# blend: laws-imported.blend:12
law Zero.LAW.plus_zero_twice:
  for +x: Nat
  {Zero.plus(Zero.plus(x, Zero.zero()), Zero.zero()) == x : Nat}

# blend: lib/adds.blend:10
law Zero.LAW.plus_zero:
  for +x: Nat
  {Zero.plus(x, Zero.zero()) == x : Nat}

# blend: lib/adds.blend:10
law Again.LAW.plus_zero.Adds:
  for +x: Nat
  {Again.plus(x, Again.zero()) == x : Nat}

# blend: lib/adds.blend:10
law Again.LAW.plus_zero:
  for +x: Nat
  {Again.plus(x, Again.zero()) == x : Nat}

# blend: lib/adds.blend:13
def Zero.LAW.plus_zero(x):
  match x:
    case 0n:
      {==}
    case 1n+p:
      %Zero.LAW.plus_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

# blend: laws-imported.blend:15
def Zero.LAW.plus_zero_twice(x):
  %Zero.LAW.plus_zero(x) : {Nat.add(Nat.add(x, 0n), 0n) == _ : Nat}
  Zero.LAW.plus_zero(Nat.add(x, 0n))

# blend: lib/adds.blend:13
def Again.LAW.plus_zero.Adds(x):
  match x:
    case 0n:
      {==}
    case 1n+p:
      %Again.LAW.plus_zero.Adds(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

# blend: laws-imported.blend:22
def Again.LAW.plus_zero(x):
  Again.LAW.plus_zero.Adds(x)
