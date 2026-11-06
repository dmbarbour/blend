# Whether `&&` and `||` short-circuit in a native build (bench/README.md):
# each case tests a value known only at run time, its right side work
# that grows with N, and nothing clang can fold. A case that
# short-circuits costs the same at N and 1,000 N; one that evaluates
# its right side, a thousand times more. Bend 2.0.39, 2026-11-06: every
# case grows, the control (4) as much as the rest, so neither operator
# short-circuits: decide on a cheap test in a helper matching a `Bool`
# parameter instead (docs/Proving.md).
#
#   bend bench/andor.bend -o andor; andor CASE N
#   0: c && work       c false
#   1: x == 2 && work  x 1
#   2: (x == 2 && work) || d   x 1, d false
#   3: x == 1 || work  x 1
#   4: x == 1 && work  x 1: the control, its right side wanted
import Base

def mix(xs: List<&2, U32>, +acc: U32) -> U32:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      mix(t, (acc * 31 + h : U32))

# work that grows with n, its result depending on it
def work(+n: Nat) -> Bool:
  U32.is_eq(mix(List.replicate(U32, n, 1), 0), 7)

def c0(+c: Bool, +n: Nat) -> Bool:
  c && work(n)

def c1(+x: U32, +n: Nat) -> Bool:
  U32.is_eq(x, 2) && work(n)

def c2(+x: U32, +n: Nat, +d: Bool) -> Bool:
  (U32.is_eq(x, 2) && work(n)) || d

def c3(+x: U32, +n: Nat) -> Bool:
  U32.is_eq(x, 1) || work(n)

def c4(+x: U32, +n: Nat) -> Bool:
  U32.is_eq(x, 1) && work(n)

def pick.k(+a: Bool, +b: Bool, +c: Bool, +d: Bool, +x: U32, +n: Nat) -> Bool:
  match a:
    case True{}:
      c0(U32.is_eq(x, 2), n)
    case False{}:
      match b:
        case True{}:
          c1(x, n)
        case False{}:
          match c:
            case True{}:
              c2(x, n, False{})
            case False{}:
              match d:
                case True{}:
                  c3(x, n)
                case False{}:
                  c4(x, n)

def pick(+w: U32, +x: U32, +n: Nat) -> Bool:
  pick.k(U32.is_eq(w, 0), U32.is_eq(w, 1), U32.is_eq(w, 2), U32.is_eq(w, 3), x, n)

def shown(+b: Bool) -> String:
  match b:
    case True{}:
      "T"
    case False{}:
      "F"

def main.args(xs: List<String>) -> IO(Unit):
  match xs:
    case Con{prog, rest}:
      match rest:
        case Con{+w, more}:
          match more:
            case Con{num, extra}:
              IO.print(shown(pick(Maybe.default(&2, U32, U32.read(w), 0), 1, U32.to_nat(Maybe.default(&2, U32, U32.read(num), 0)))))
            case Nil{}:
              IO.print("usage: andor CASE N")
        case Nil{}:
          IO.print("usage: andor CASE N")
    case Nil{}:
      IO.print("usage: andor CASE N")

def main() -> IO(Unit):
  do IO<Unit>:
    xs : List<String> <- IO.args()
    main.args(xs)
