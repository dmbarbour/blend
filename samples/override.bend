# Written by Blend from override.blend; do not edit.
# blend stamp: fb5bee1f6ddd 6bfcf647302775a9
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
