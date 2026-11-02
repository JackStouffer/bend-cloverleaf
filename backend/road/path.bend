import Base
import ./search.bend as S

# Paths through a finished search. Nothing about the search is proven, so a
# lookup doesn't take its word: it walks the path the search left behind against
# the graph, adds up the arcs, and reports only what that walk confirms. A bug in
# the search shows up as a refused lookup, never as a wrong drive time.

# Reading the path back
# ---------------------

type Back is Type:
  Back{w: Array<U32>, path: List<&2, U32>}

type Hopping is Data:
  AtArc{}
  AtTail{}
  AtStep{}

# Follows tail words from `at` back to src, gathering arcs. Each hop takes 3 steps
# of fuel, so 3 per node covers any path. One that runs out has a cycle, stops
# short and fails the walk.
def Back.go(fuel: Nat, m: Hopping, b: Bool, +n: U32, +src: U32, +at: U32, +a: U32, path: List<&2, U32>, p: Array<U32> & U32) -> Back:
  match fuel:
    case 0n:
      (w, _) = p
      Back{w, path}
    case 1n+f:
      match m:
        case AtArc{}:
          (w, +v) = p
          Back.go(f, AtTail{}, False{}, n, src, at, v, path, Array.get(U32, w, ((3 * n : U32) + at : U32)))
        case AtTail{}:
          (w, +v) = p
          Back.go(f, AtStep{}, U32.is_eq(v, src), n, src, v, a, a <> path, (w, 0))
        case AtStep{}:
          match b:
            case True{}:
              (w, _) = p
              Back{w, path}
            case False{}:
              (w, _) = p
              Back.go(f, AtArc{}, False{}, n, src, at, a, path, Array.get(U32, w, ((2 * n : U32) + at : U32)))

# The arcs from src to at, in travel order. src to itself is no arcs at all.
def Back.read(c: Bool, +fuel: Nat, +n: U32, +src: U32, +at: U32, w: Array<U32>) -> Back:
  match c:
    case True{}:
      Back{w, Nil{}}
    case False{}:
      Back.go(fuel, AtArc{}, False{}, n, src, at, 0, Nil{}, Array.get(U32, w, ((2 * n : U32) + at : U32)))

# Walking a path
# --------------

# Where a walk has got to. `ok` goes false at the first arc that isn't there.
type Hop is Type:
  Hop{g: Array<U32>, at: U32, total: Nat, ok: Bool}

def Hop.cost(p: Array<U32> & U32, +head: U32, +total: Nat) -> Hop:
  (g, +c) = p
  Hop{g, head, Nat.add(total, U32.to_nat(c)), True{}}

def Hop.head(p: Array<U32> & U32, +n: U32, +a: U32, +total: Nat) -> Hop:
  (g, +head) = p
  Hop.cost(Array.get(U32, g, (n + (2 * a : U32) + 5 : U32)), head, total)

def Hop.inside(c: Bool, g: Array<U32>, +n: U32, +a: U32, +at: U32, +total: Nat) -> Hop:
  match c:
    case True{}:
      Hop.head(Array.get(U32, g, (n + (2 * a : U32) + 4 : U32)), n, a, total)
    case False{}:
      Hop{g, at, total, False{}}

def Hop.hi(p: Array<U32> & U32, +lo: U32, +n: U32, +a: U32, +at: U32, +total: Nat) -> Hop:
  (g, +hi) = p
  Hop.inside(U32.is_lt(at, n) && U32.is_le(lo, a) && U32.is_lt(a, hi), g, n, a, at, total)

def Hop.lo(p: Array<U32> & U32, +n: U32, +a: U32, +at: U32, +total: Nat) -> Hop:
  (g, +lo) = p
  Hop.hi(Array.get(U32, g, (at + 3 : U32)), lo, n, a, at, total)

def Hop.go(ok: Bool, g: Array<U32>, +n: U32, +a: U32, +at: U32, +total: Nat) -> Hop:
  match ok:
    case True{}:
      Hop.lo(Array.get(U32, g, (at + 2 : U32)), n, a, at, total)
    case False{}:
      Hop{g, at, total, False{}}

def Hop.step(h: Hop, +n: U32, +a: U32) -> Hop:
  match h:
    case Hop{g, +at, +total, ok}:
      Hop.go(ok, g, n, a, at, total)

def Path.walk(xs: List<&2, U32>, h: Hop, +n: U32) -> Hop:
  match xs:
    case Nil{}:
      h
    case +a <> t:
      Path.walk(t, Hop.step(h, n, a), n)

# The walk's result: the graph back, and the cost if every arc was there and the
# walk ended on dst.
type Walked is Type:
  Walked{g: Array<U32>, cost: Maybe<&2, Nat>}

def Path.end.at(c: Bool, g: Array<U32>, +total: Nat) -> Walked:
  match c:
    case True{}:
      Walked{g, Some{total}}
    case False{}:
      Walked{g, None{}}

def Path.end(h: Hop, +dst: U32) -> Walked:
  match h:
    case Hop{g, +at, +total, ok}:
      Path.end.at(ok && U32.is_eq(at, dst), g, total)

def Path.check(g: Array<U32>, +n: U32, +src: U32, +dst: U32, xs: List<&2, U32>) -> Walked:
  Path.end(Path.walk(xs, Hop{g, src, 0n, True{}}, n), dst)

# Reporting a drive time
# ----------------------

# One finished lookup. `refused` means the search claimed a time that the walk
# didn't confirm, which only a bug can cause.
type Cell is Type:
  Cell{g: Array<U32>, w: Array<U32>, path: List<&2, U32>, cost: Maybe<&2, Nat>, refused: Bool}

def Cell.agree(c: Bool, g: Array<U32>, w: Array<U32>, +path: List<&2, U32>, +t: Nat) -> Cell:
  match c:
    case True{}:
      Cell{g, w, path, Some{t}, False{}}
    case False{}:
      Cell{g, w, Nil{}, None{}, True{}}

def Cell.judge(c: Maybe<&2, Nat>, g: Array<U32>, w: Array<U32>, +path: List<&2, U32>, +d: Nat, +limit: Nat) -> Cell:
  match c:
    case None{}:
      Cell{g, w, Nil{}, None{}, True{}}
    case Some{+t}:
      Cell.agree(Nat.is_eq(t, d) && Nat.is_le(t, limit), g, w, path, t)

def Cell.end(x: Walked, w: Array<U32>, +path: List<&2, U32>, +d: Nat, +limit: Nat) -> Cell:
  match x:
    case Walked{g, c}:
      Cell.judge(c, g, w, path, d, limit)

def Cell.walk(b: Back, g: Array<U32>, +n: U32, +src: U32, +dst: U32, +d: U32, +limit: U32) -> Cell:
  match b:
    case Back{w, +path}:
      Cell.end(Path.check(g, n, src, dst, path), w, path, U32.to_nat(d), U32.to_nat(limit))

def Cell.dist(p: Array<U32> & U32, g: Array<U32>, +fuel: Nat, +n: U32, +limit: U32, +src: U32, +dst: U32) -> Cell:
  (w, +d) = p
  Cell.walk(Back.read(U32.is_eq(src, dst), fuel, n, src, dst, w), g, n, src, dst, d, limit)

def Cell.seen(c: Bool, g: Array<U32>, w: Array<U32>, +fuel: Nat, +n: U32, +limit: U32, +src: U32, +dst: U32) -> Cell:
  match c:
    case True{}:
      Cell.dist(Array.get(U32, w, dst), g, fuel, n, limit, src, dst)
    case False{}:
      Cell{g, w, Nil{}, None{}, False{}}

def Cell.stamp(p: Array<U32> & U32, g: Array<U32>, +fuel: Nat, +n: U32, +limit: U32, +src: U32, +dst: U32, +stamp: U32) -> Cell:
  (w, +s) = p
  Cell.seen(U32.is_eq(s, stamp), g, w, fuel, n, limit, src, dst)

# The drive time from src to dst after a finished search with this stamp. None
# means dst is out of reach within the limit.
def Cell.read(g: Array<U32>, w: Array<U32>, +fuel: Nat, +n: U32, +limit: U32, +src: U32, +dst: U32, +stamp: U32) -> Cell:
  Cell.stamp(Array.get(U32, w, (n + dst : U32)), g, fuel, n, limit, src, dst, stamp)

def Walked.cost(x: Walked) -> Maybe<&2, Nat>:
  match x:
    case Walked{_, +c}:
      c

def Cell.cost(c: Cell) -> Maybe<&2, Nat>:
  match c:
    case Cell{_, _, _, +x, _}:
      x

def Cell.path(c: Cell) -> List<&2, U32>:
  match c:
    case Cell{_, _, +x, _, _}:
      x

def Cell.graph(c: Cell) -> Array<U32>:
  match c:
    case Cell{g, _, _, _, _}:
      g
