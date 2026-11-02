import Base

# What the road laws mean, in plain numbers over the graph's words. Nothing here
# runs: laws state their claims with these defs, so a bug in the code being
# checked can't change what the claim says.

def Fst(p: Array<U32> & U32) -> Array<U32>:
  (a, x) = p
  a

def Snd(p: Array<U32> & U32) -> U32:
  (a, x) = p
  x

# Word i of an array.
def At(a: Array<U32>, +i: U32) -> U32:
  Snd(Array.get(U32, a, i))

# Arc number a leaves node `at`: `at` is a node, and a lies between its first arc
# and the next node's.
def Leaves(-g: Array<U32>, +n: U32, +at: U32, +a: U32) -> Type:
  {U32.is_lt(at, n) && U32.is_le(At(g, (at + 2 : U32)), a) && U32.is_lt(a, At(g, (at + 3 : U32))) == True{} : Bool}

def Head(g: Array<U32>, +n: U32, +a: U32) -> U32:
  At(g, (n + (2 * a : U32) + 4 : U32))

def Cost(g: Array<U32>, +n: U32, +a: U32) -> Nat:
  U32.to_nat(At(g, (n + (2 * a : U32) + 5 : U32)))

# The path goes from `at` to dst along arcs that are in the graph, and adding its
# arcs' costs to sofar gives cost.
def Walks(path: List<&2, U32>, -g: Array<U32>, +n: U32, +at: U32, +dst: U32, +sofar: Nat, +cost: Nat) -> Type:
  match path:
    case Nil{}:
      {U32.is_eq(at, dst) == True{} : Bool} & {sofar == cost : Nat}
    case +a <> t:
      Leaves(g, n, at, a) & Walks(t, g, n, Head(g, n, a), dst, Nat.add(sofar, Cost(g, n, a)), cost)
