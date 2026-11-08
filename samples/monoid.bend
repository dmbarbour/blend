# Written by Blend from monoid.blend; do not edit.
# blend stamp: 52e1a411e187 6b7267d4f0bf1ec8
import Base

# blend: monoid.blend:11
def AnyOf.T() -> Data: Bool

# blend: monoid.blend:12
def AnyOf.zero() -> AnyOf.T():
  False{}

# blend: monoid.blend:14
def AnyOf.op(+a: AnyOf.T(), +b: AnyOf.T()) -> AnyOf.T():
  a || b

# blend: monoid.blend:23
def main() -> IO(Unit):
  IO.print(Bool.show(AnyOf.op(True{}, AnyOf.zero())))

# blend: monoid.blend:6
law AnyOf.LAW.right_id:
  for +x: AnyOf.T()
  {AnyOf.op(x, AnyOf.zero()) == x : AnyOf.T()}

# blend: monoid.blend:16
def AnyOf.LAW.right_id(x):
  match x:
    case True{}:
      {==}
    case False{}:
      {==}
