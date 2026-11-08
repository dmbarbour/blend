# Written by Blend from laws.blend; do not edit.
# blend stamp: c2332520f07f 904be2ff2d50eb39
import Base

# blend: laws.blend:31
def NatAdd.T() -> Data: Nat

# blend: laws.blend:32
def NatAdd.zero() -> NatAdd.T():
  0n

# blend: laws.blend:34
def NatAdd.op(+a: NatAdd.T(), +b: NatAdd.T()) -> NatAdd.T():
  Nat.add(a, b)

# blend: laws.blend:17
def NatAdd.double(+x: NatAdd.T()) -> NatAdd.T():
  NatAdd.op(x, x)

# blend: laws.blend:58
def AnyOf.T() -> Data: Bool

# blend: laws.blend:59
def AnyOf.zero() -> AnyOf.T():
  False{}

# blend: laws.blend:61
def AnyOf.op(+a: AnyOf.T(), +b: AnyOf.T()) -> AnyOf.T():
  a || b

# blend: laws.blend:63
def AnyOf.double(+x: AnyOf.T()) -> AnyOf.T():
  x

# blend: laws.blend:92
def main() -> IO(Unit):
  IO.print(Nat.show(NatAdd.double(3n)) ++ " " ++ Bool.show(AnyOf.double(True{})))

# blend: laws.blend:50
law NatAdd.LAW.op_succ:
  for +a: NatAdd.T()
  for +b: NatAdd.T()
  {1n+NatAdd.op(a, b) == NatAdd.op(a, 1n+b) : NatAdd.T()}

# blend: laws.blend:19
law NatAdd.LAW.right_id:
  for +x: NatAdd.T()
  {NatAdd.op(x, NatAdd.zero()) == x : NatAdd.T()}

# blend: laws.blend:22
law NatAdd.LAW.double_op:
  for +x: NatAdd.T()
  {NatAdd.double(x) == NatAdd.op(x, x) : NatAdd.T()}

# blend: laws.blend:19
law AnyOf.LAW.right_id:
  for +x: AnyOf.T()
  {AnyOf.op(x, AnyOf.zero()) == x : AnyOf.T()}

# blend: laws.blend:22
law AnyOf.LAW.double_op:
  for +x: AnyOf.T()
  {AnyOf.double(x) == AnyOf.op(x, x) : AnyOf.T()}

# blend: laws.blend:86
law LAW.double_three:
  {NatAdd.double(3n) == 6n : Nat}

# blend: laws.blend:36
def NatAdd.LAW.right_id(x):
  match x:
    case 0n:
      {==}
    case 1n+p:
      %NatAdd.LAW.right_id(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

# blend: laws.blend:43
def NatAdd.LAW.add_succ(a: Nat, -b: Nat) -> {1n+Nat.add(a, b) == Nat.add(a, 1n+b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %NatAdd.LAW.add_succ(p, b) : {2n+Nat.add(p, b) == 1n+_ : Nat}
      {==}

# blend: laws.blend:54
def NatAdd.LAW.op_succ(a, b):
  NatAdd.LAW.add_succ(a, b)

# blend: laws.blend:25
def NatAdd.LAW.op_double(x: NatAdd.T()) -> {NatAdd.op(x, x) == NatAdd.double(x) : NatAdd.T()}:
  {==}

# blend: laws.blend:27
def NatAdd.LAW.double_op(x):
  {==}

# blend: laws.blend:65
def AnyOf.LAW.right_id(x):
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

# blend: laws.blend:71
def AnyOf.LAW.double_op(x):
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

# blend: laws.blend:77
def AnyOf.LAW.op_double(x: AnyOf.T()) -> {AnyOf.op(x, x) == AnyOf.double(x) : AnyOf.T()}:
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

# blend: laws.blend:89
def LAW.double_three():
  {==}
