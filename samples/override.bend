# Written by Blend from override.blend; do not edit.
# blend stamp: 78e54ed99292 ae7718405fd67268
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
