# Written by Blend from override.blend; do not edit.
# blend stamp: bedd1e213079 366e8504079dd9e2
import Base

# blend: override.blend:4
def Greeter.greet() -> String:
  "hello"

# blend: override.blend:6
def Greeter.show() -> String:
  Greeter.greet() ++ ", world"

# blend: override.blend:10
def Loud.greet() -> String:
  "HELLO"

# blend: override.blend:6
def Loud.show() -> String:
  Loud.greet() ++ ", world"

# blend: override.blend:13
def main() -> IO(Unit):
  IO.print(Greeter.show() ++ " / " ++ Loud.show())
