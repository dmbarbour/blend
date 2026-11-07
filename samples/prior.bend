# Written by Blend from prior.blend; do not edit.
# blend stamp: 93f00e14ee3f 138c00e7a073a449
import Base

# blend: prior.blend:4
def Plain.tag() -> String:
  "plain"

# blend: prior.blend:4
def Bold.tag.Plain() -> String:
  "plain"

# blend: prior.blend:8
def Bold.tag() -> String:
  "*" ++ Bold.tag.Plain() ++ "*"

# blend: prior.blend:4
def Loud.tag.Plain() -> String:
  "plain"

# blend: prior.blend:12
def Loud.tag() -> String:
  Loud.tag.Plain() ++ "!"

# blend: prior.blend:4
def BoldLoud.tag.Plain() -> String:
  "plain"

# blend: prior.blend:12
def BoldLoud.tag.Loud() -> String:
  BoldLoud.tag.Plain() ++ "!"

# blend: prior.blend:8
def BoldLoud.tag() -> String:
  "*" ++ BoldLoud.tag.Loud() ++ "*"

# blend: prior.blend:17
def main() -> IO(Unit):
  IO.print(Plain.tag() ++ " " ++ Bold.tag() ++ " " ++ Loud.tag() ++ " " ++ BoldLoud.tag())
