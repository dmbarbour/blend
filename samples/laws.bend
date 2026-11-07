# Written by Blend from laws.blend; do not edit.
# blend stamp: 93f00e14ee3f 0b62acdda9a71ba1
import Base

# blend: laws.blend:28
def NatAdd.T() -> Data: Nat

# blend: laws.blend:29
def NatAdd.zero() -> NatAdd.T():
  0n

# blend: laws.blend:31
def NatAdd.op(+a: NatAdd.T(), +b: NatAdd.T()) -> NatAdd.T():
  Nat.add(a, b)

# blend: laws.blend:16
def NatAdd.double(+x: NatAdd.T()) -> NatAdd.T():
  NatAdd.op(x, x)

# blend: laws.blend:55
def AnyOf.T() -> Data: Bool

# blend: laws.blend:56
def AnyOf.zero() -> AnyOf.T():
  False{}

# blend: laws.blend:58
def AnyOf.op(+a: AnyOf.T(), +b: AnyOf.T()) -> AnyOf.T():
  a || b

# blend: laws.blend:60
def AnyOf.double(+x: AnyOf.T()) -> AnyOf.T():
  x

# blend: laws.blend:83
def main() -> IO(Unit):
  IO.print(Nat.show(NatAdd.double(3n)) ++ " " ++ Bool.show(AnyOf.double(True{})))

# blend: laws.blend:47
law NatAdd.LAW.op_succ:
  for +a: NatAdd.T()
  for +b: NatAdd.T()
  {1n+NatAdd.op(a, b) == NatAdd.op(a, 1n+b) : NatAdd.T()}

# blend: laws.blend:18
law NatAdd.LAW.right_id:
  for +x: NatAdd.T()
  {NatAdd.op(x, NatAdd.zero()) == x : NatAdd.T()}

# blend: laws.blend:21
law NatAdd.LAW.double_op:
  for +x: NatAdd.T()
  {NatAdd.double(x) == NatAdd.op(x, x) : NatAdd.T()}

# blend: laws.blend:18
law AnyOf.LAW.right_id:
  for +x: AnyOf.T()
  {AnyOf.op(x, AnyOf.zero()) == x : AnyOf.T()}

# blend: laws.blend:21
law AnyOf.LAW.double_op:
  for +x: AnyOf.T()
  {AnyOf.double(x) == AnyOf.op(x, x) : AnyOf.T()}

# blend: laws.blend:77
law LAW.double_three:
  {NatAdd.double(3n) == 6n : Nat}

# blend: laws.blend:33
def NatAdd.LAW.right_id(x):
  match x:
    case 0n:
      {==}
    case 1n+p:
      %NatAdd.LAW.right_id(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

# blend: laws.blend:40
def NatAdd.LAW.add_succ(a: Nat, -b: Nat) -> {1n+Nat.add(a, b) == Nat.add(a, 1n+b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %NatAdd.LAW.add_succ(p, b) : {2n+Nat.add(p, b) == 1n+_ : Nat}
      {==}

# blend: laws.blend:51
def NatAdd.LAW.op_succ(a, b):
  NatAdd.LAW.add_succ(a, b)

# blend: laws.blend:24
def NatAdd.LAW.double_op(x):
  {==}

# blend: laws.blend:62
def AnyOf.LAW.right_id(x):
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

# blend: laws.blend:68
def AnyOf.LAW.double_op(x):
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

# blend: laws.blend:80
def LAW.double_three():
  {==}
