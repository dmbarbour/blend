# Written by Blend from nested.blend; do not edit.
# blend stamp: fb5bee1f6ddd ed2176abdd940959
import Base

# blend: nested.blend:3
def unit() -> String:
  "m"

# blend: nested.blend:7
def Outer.name() -> String:
  "outer"

# blend: nested.blend:10
def Outer.Inner.name() -> String:
  "inner"

# blend: nested.blend:12
def Outer.Inner.path() -> String:
  Outer.name() ++ "." ++ Outer.Inner.name() ++ "." ++ unit()

# blend: nested.blend:15
def main() -> IO(Unit):
  IO.print(Outer.Inner.path())
