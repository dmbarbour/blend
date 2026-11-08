# Written by Blend from declares.blend; do not edit.
# blend stamp: 6a79f2029262 ca5a428d3176f145
import Base

# blend: declares.blend:12
def Listed.S() -> Data: List<&2, U32>

# blend: declares.blend:13
def Listed.empty() -> Listed.S():
  Nil{}

# blend: declares.blend:15
def Listed.push(st: Listed.S(), +x: U32) -> Listed.S():
  Con{x, st}

# blend: declares.blend:17
def Listed.size(st: Listed.S()) -> U32:
  U32.from_nat(List.length(&2, U32, st))

# blend: declares.blend:8
def Listed.one(+x: U32) -> Listed.S():
  Listed.push(Listed.empty(), x)

# blend: declares.blend:21
def Counted.S() -> Data: U32

# blend: declares.blend:22
def Counted.empty() -> Counted.S():
  0

# blend: declares.blend:24
def Counted.push(+st: Counted.S(), +x: U32) -> Counted.S():
  (st + x : U32)

# blend: declares.blend:26
def Counted.size(+st: Counted.S()) -> U32:
  st

# blend: declares.blend:8
def Counted.one(+x: U32) -> Counted.S():
  Counted.push(Counted.empty(), x)

# blend: declares.blend:29
def main() -> IO(Unit):
  IO.print(U32.show(Listed.size(Listed.one(5))) ++ " " ++ U32.show(Counted.size(Counted.one(5))))

# blend: declares.blend:4
def Listed.LAW.S.as_declared() -> Data: Listed.S()

# blend: declares.blend:5
def Listed.LAW.push.as_declared(st: Listed.S(), +x: U32) -> Listed.S(): Listed.push(st, x)

# blend: declares.blend:6
def Listed.LAW.empty.as_declared() -> Listed.S(): Listed.empty()

# blend: declares.blend:4
def Counted.LAW.S.as_declared() -> Data: Counted.S()

# blend: declares.blend:5
def Counted.LAW.push.as_declared(st: Counted.S(), +x: U32) -> Counted.S(): Counted.push(st, x)

# blend: declares.blend:6
def Counted.LAW.empty.as_declared() -> Counted.S(): Counted.empty()
