# Written by Blend from monads.blend; do not edit.
# blend stamp: 5291f54add10 76d386aac49f8848
import Base

# blend: monads.blend:19
def Opt.pure(-A: Data, x: A) -> Maybe<&2, A>:
  Some{x}

# blend: monads.blend:21
def Opt.bind(-A: Data, -B: Data, m: Maybe<&2, A>, f: A -> Maybe<&2, B>) -> Maybe<&2, B>:
  match m:
    case None{}:
      None{}
    case Some{x}:
      f(x)

# blend: monads.blend:12
def Opt.both(a: Maybe<&2, U32>, b: Maybe<&2, U32>) -> Maybe<&2, U32>:
  do Opt<U32>:  # Opt.bind Opt.pure
    x : U32 <- a
    y : U32 <- b
    return (x + y : U32)

# blend: monads.blend:29
def Loud.pure(-A: Data, x: A) -> Maybe<&2, A>:
  None{}

# blend: monads.blend:21
def Loud.bind(-A: Data, -B: Data, m: Maybe<&2, A>, f: A -> Maybe<&2, B>) -> Maybe<&2, B>:
  match m:
    case None{}:
      None{}
    case Some{x}:
      f(x)

# blend: monads.blend:12
def Loud.both(a: Maybe<&2, U32>, b: Maybe<&2, U32>) -> Maybe<&2, U32>:
  do Loud<U32>:  # Loud.bind Loud.pure
    x : U32 <- a
    y : U32 <- b
    return (x + y : U32)

# blend: monads.blend:32
def say(m: Maybe<&2, U32>) -> String:
  match m:
    case None{}:
      "none"
    case Some{v}:
      U32.show(v)

# blend: monads.blend:39
def more(a: Maybe<&2, U32>) -> Maybe<&2, U32>:
  do Opt<U32>:  # Opt.bind Opt.pure
    x : U32 <- a
    return (x + 3 : U32)

# blend: monads.blend:44
def main() -> IO(Unit):
  IO.print(say(Opt.both(Some{3}, Some{4})) ++ " " ++ say(Loud.both(Some{3}, Some{4})) ++ " " ++ say(more(Some{1})))
