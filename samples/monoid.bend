# Written by Blend from monoid.blend; do not edit.
import Base

# blend: monoid.blend:16
def AnyOf.T() -> Data: Bool

# blend: monoid.blend:17
def AnyOf.zero() -> AnyOf.T():
  False{}

# blend: monoid.blend:19
def AnyOf.op(+a: AnyOf.T(), +b: AnyOf.T()) -> AnyOf.T():
  a || b

# blend: monoid.blend:29
def AllOf.T() -> Data: Bool

# blend: monoid.blend:30
def AllOf.zero() -> AllOf.T():
  True{}

# blend: monoid.blend:32
def AllOf.op(+a: AllOf.T(), +b: AllOf.T()) -> AllOf.T():
  a && b

# blend: monoid.blend:41
def main() -> IO(Unit):
  IO.print(Bool.show(AnyOf.op(True{}, AnyOf.zero())) ++ " " ++ Bool.show(AllOf.op(True{}, AllOf.zero())))

# blend: monoid.blend:11
law AnyOf.LAW.right_id:
  for +x: AnyOf.T()
  {AnyOf.op(x, AnyOf.zero()) == x : AnyOf.T()}

# blend: monoid.blend:11
law AllOf.LAW.right_id:
  for +x: AllOf.T()
  {AllOf.op(x, AllOf.zero()) == x : AllOf.T()}

# blend: monoid.blend:21
def AnyOf.LAW.right_id(x):
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

# blend: monoid.blend:34
def AllOf.LAW.right_id(x):
  match x:
    case True{}:
      {==}
    case False{}:
      {==}
