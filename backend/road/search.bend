import Base

# Bounded Dijkstra over one state's road graph. Pure: it takes arrays and gives
# them back. It's a Nat-fuel loop with a mode argument, because the search's
# steps tail-call each other and checked defs can't be mutually recursive.
#
# An array read answers a pair, and a pair from a computed value can't be
# destructured where it's made. So each loop takes its last read as a parameter
# and each mode picks up where the last read left off. `gp` and `wp` are those
# pairs for the graph and the workspace. The graph is only ever read.
#
# g: g[0] nodes, g[1] arcs, first arc per node from slot 2, then arcs from slot
#    n + 4 as (head, deciseconds).
# w: dist at 0, stamp at n, arc at 2n, tail at 3n, then the heap from 4n as
#    (key, node) pairs. Slot 1 of the heap region is its root, so the children
#    of i are 2i and 2i + 1. A stamp saves clearing the workspace per search.

# Heap
# ----

def word(c: Bool, +a: U32, +b: U32) -> U32:
  match c:
    case True{}:
      a
    case False{}:
      b

def Heap.put(w: Array<U32>, +h: U32, +i: U32, +key: U32, +node: U32) -> Array<U32>:
  +at = (h + (2 * i : U32) : U32)
  Array.set(U32, Array.set(U32, w, at, key), (at + 1 : U32), node)

type Sink is Data:
  SinkLook{}
  SinkHas{}
  SinkLeft{}
  SinkPick{}
  SinkLess{}
  SinkMove{}

# Moves (key, node) down from slot i. `c` is the smaller child and `ck` its key.
# fuel only guards termination: the heap's depth is under 32 levels.
def Heap.sink(fuel: Nat, m: Sink, b: Bool, +h: U32, +size: U32, +i: U32, +key: U32, +node: U32, +c: U32, +ck: U32, p: Array<U32> & U32) -> Array<U32>:
  match fuel:
    case 0n:
      (w, _) = p
      Heap.put(w, h, i, key, node)
    case 1n+f:
      match m:
        case SinkLook{}:
          +left = (2 * i : U32)
          Heap.sink(f, SinkHas{}, U32.is_le(left, size), h, size, i, key, node, left, ck, p)
        case SinkHas{}:
          match b:
            case True{}:
              (w, _) = p
              Heap.sink(f, SinkLeft{}, False{}, h, size, i, key, node, c, ck, Array.get(U32, w, (h + (2 * c : U32) : U32)))
            case False{}:
              (w, _) = p
              Heap.put(w, h, i, key, node)
        case SinkLeft{}:
          (w, +l) = p
          Heap.sink(f, SinkPick{}, U32.is_lt(c, size), h, size, i, key, node, c, l, Array.get(U32, w, (h + (2 * c : U32) + 2 : U32)))
        case SinkPick{}:
          (w, +r) = p
          +right = b && U32.is_lt(r, ck)
          +best = word(right, r, ck)
          Heap.sink(f, SinkLess{}, U32.is_lt(best, key), h, size, i, key, node, word(right, (c + 1 : U32), c), best, (w, 0))
        case SinkLess{}:
          match b:
            case True{}:
              (w, _) = p
              Heap.sink(f, SinkMove{}, False{}, h, size, i, key, node, c, ck, Array.get(U32, w, (h + (2 * c : U32) + 1 : U32)))
            case False{}:
              (w, _) = p
              Heap.put(w, h, i, key, node)
        case SinkMove{}:
          (w, +cn) = p
          Heap.sink(f, SinkLook{}, False{}, h, size, c, key, node, c, ck, (Heap.put(w, h, i, ck, cn), 0))

type Rise is Data:
  RiseLook{}
  RiseTop{}
  RiseKey{}
  RiseLess{}
  RiseMove{}

# Moves (key, node) up from slot i. `k` is the parent's key.
def Heap.rise(fuel: Nat, m: Rise, b: Bool, +h: U32, +i: U32, +key: U32, +node: U32, +k: U32, p: Array<U32> & U32) -> Array<U32>:
  match fuel:
    case 0n:
      (w, _) = p
      Heap.put(w, h, i, key, node)
    case 1n+f:
      match m:
        case RiseLook{}:
          Heap.rise(f, RiseTop{}, U32.is_le(i, 1), h, i, key, node, k, p)
        case RiseTop{}:
          match b:
            case True{}:
              (w, _) = p
              Heap.put(w, h, i, key, node)
            case False{}:
              (w, _) = p
              Heap.rise(f, RiseKey{}, False{}, h, i, key, node, k, Array.get(U32, w, (h + (2 * U32.shr(i) : U32) : U32)))
        case RiseKey{}:
          (w, +pk) = p
          Heap.rise(f, RiseLess{}, U32.is_lt(key, pk), h, i, key, node, pk, (w, 0))
        case RiseLess{}:
          match b:
            case True{}:
              (w, _) = p
              Heap.rise(f, RiseMove{}, False{}, h, i, key, node, k, Array.get(U32, w, (h + (2 * U32.shr(i) : U32) + 1 : U32)))
            case False{}:
              (w, _) = p
              Heap.put(w, h, i, key, node)
        case RiseMove{}:
          (w, +pn) = p
          Heap.rise(f, RiseLook{}, False{}, h, U32.shr(i), key, node, k, (Heap.put(w, h, i, k, pn), 0))

# Relaxing an arc
# ---------------

def Full() -> U32:
  4294967295

# What a relaxation leaves behind: the workspace and the heap's new size, or
# Full if the heap has no room.
def Relax.push(+full: Bool, w: Array<U32>, +hf: Nat, +n: U32, +h: U32, +size: U32, +stamp: U32, +a: U32, +tail: U32, +t: U32, +nd: U32) -> Array<U32> & U32:
  match full:
    case True{}:
      (w, Full())
    case False{}:
      +m = (size + 1 : U32)
      w1 = Array.set(U32, Array.set(U32, w, t, nd), (n + t : U32), stamp)
      w2 = Array.set(U32, Array.set(U32, w1, ((2 * n : U32) + t : U32), a), ((3 * n : U32) + t : U32), tail)
      (Heap.rise(hf, RiseLook{}, False{}, h, m, nd, t, 0, (w2, 0)), m)

def Relax.better(c: Bool, w: Array<U32>, +hf: Nat, +n: U32, +h: U32, +cap: U32, +size: U32, +stamp: U32, +a: U32, +tail: U32, +t: U32, +nd: U32) -> Array<U32> & U32:
  match c:
    case True{}:
      Relax.push(U32.is_eq(size, cap), w, hf, n, h, size, stamp, a, tail, t, nd)
    case False{}:
      (w, size)

def Relax.old(p: Array<U32> & U32, +hf: Nat, +n: U32, +h: U32, +cap: U32, +size: U32, +stamp: U32, +a: U32, +tail: U32, +t: U32, +nd: U32) -> Array<U32> & U32:
  (w, +old) = p
  Relax.better(U32.is_lt(nd, old), w, hf, n, h, cap, size, stamp, a, tail, t, nd)

def Relax.seen(c: Bool, w: Array<U32>, +hf: Nat, +n: U32, +h: U32, +cap: U32, +size: U32, +stamp: U32, +a: U32, +tail: U32, +t: U32, +nd: U32) -> Array<U32> & U32:
  match c:
    case True{}:
      Relax.old(Array.get(U32, w, t), hf, n, h, cap, size, stamp, a, tail, t, nd)
    case False{}:
      Relax.better(True{}, w, hf, n, h, cap, size, stamp, a, tail, t, nd)

def Relax.stamp(p: Array<U32> & U32, +hf: Nat, +n: U32, +h: U32, +cap: U32, +size: U32, +stamp: U32, +a: U32, +tail: U32, +t: U32, +nd: U32) -> Array<U32> & U32:
  (w, +s) = p
  Relax.seen(U32.is_eq(s, stamp), w, hf, n, h, cap, size, stamp, a, tail, t, nd)

def Relax.run(w: Array<U32>, +hf: Nat, +n: U32, +h: U32, +cap: U32, +size: U32, +stamp: U32, +a: U32, +tail: U32, +t: U32, +nd: U32) -> Array<U32> & U32:
  Relax.stamp(Array.get(U32, w, (n + t : U32)), hf, n, h, cap, size, stamp, a, tail, t, nd)

# The search
# ----------

type Why is Data:
  Finished{}
  OutOfFuel{}
  HeapFull{}

# A search hands both arrays back. Only a Finished search covered everything
# within its limit.
type Out is Type:
  Out{g: Array<U32>, w: Array<U32>, settled: U32, why: Why}

type Mode is Data:
  AtNext{}
  AtRoot{}
  AtKey{}
  AtNode{}
  AtLast{}
  AtSift{}
  AtDist{}
  AtFresh{}
  AtFirst{}
  AtEnd{}
  AtArc{}
  AtHead{}
  AtCost{}
  AtNear{}
  AtBack{}
  AtRoom{}

def Out.make(gp: Array<U32> & U32, wp: Array<U32> & U32, +settled: U32, +why: Why) -> Out:
  (g, _) = gp
  (w, _) = wp
  Out{g, w, settled, why}

# `x` and `y` hold the arc's head and tentative distance, or the last heap entry.
def Search.go(f: Nat, m: Mode, b: Bool, +hf: Nat, +n: U32, +h: U32, +cap: U32, +limit: U32, +stamp: U32, +size: U32, +settled: U32, +key: U32, +node: U32, +a: U32, +e: U32, +x: U32, +y: U32, gp: Array<U32> & U32, wp: Array<U32> & U32) -> Out:
  match f:
    case 0n:
      Out.make(gp, wp, settled, OutOfFuel{})
    case 1n+k:
      match m:
        # Pop the smallest key.
        case AtNext{}:
          Search.go(k, AtRoot{}, U32.is_zero(size), hf, n, h, cap, limit, stamp, size, settled, key, node, a, e, x, y, gp, wp)
        case AtRoot{}:
          match b:
            case True{}:
              Out.make(gp, wp, settled, Finished{})
            case False{}:
              (w, _) = wp
              Search.go(k, AtKey{}, False{}, hf, n, h, cap, limit, stamp, size, settled, key, node, a, e, x, y, gp, Array.get(U32, w, (h + 2 : U32)))
        case AtKey{}:
          (w, +v) = wp
          Search.go(k, AtNode{}, False{}, hf, n, h, cap, limit, stamp, size, settled, v, node, a, e, x, y, gp, Array.get(U32, w, (h + 3 : U32)))
        case AtNode{}:
          (w, +v) = wp
          Search.go(k, AtLast{}, False{}, hf, n, h, cap, limit, stamp, size, settled, key, v, a, e, x, y, gp, Array.get(U32, w, (h + (2 * size : U32) : U32)))
        case AtLast{}:
          (w, +v) = wp
          Search.go(k, AtSift{}, False{}, hf, n, h, cap, limit, stamp, size, settled, key, node, a, e, v, y, gp, Array.get(U32, w, (h + (2 * size : U32) + 1 : U32)))
        case AtSift{}:
          (w, +v) = wp
          +left = (size - 1 : U32)
          Search.go(k, AtDist{}, False{}, hf, n, h, cap, limit, stamp, left, settled, key, node, a, e, x, y, gp, Array.get(U32, Heap.sink(hf, SinkLook{}, False{}, h, left, 1, x, v, 0, 0, (w, 0)), node))
        # A key older than the node's distance is a stale entry.
        case AtDist{}:
          (w, +d) = wp
          Search.go(k, AtFresh{}, U32.is_eq(d, key), hf, n, h, cap, limit, stamp, size, settled, key, node, a, e, x, y, gp, (w, 0))
        case AtFresh{}:
          match b:
            case True{}:
              (g, _) = gp
              Search.go(k, AtFirst{}, False{}, hf, n, h, cap, limit, stamp, size, (settled + 1 : U32), key, node, a, e, x, y, Array.get(U32, g, (node + 2 : U32)), wp)
            case False{}:
              Search.go(k, AtNext{}, False{}, hf, n, h, cap, limit, stamp, size, settled, key, node, a, e, x, y, gp, wp)
        # Walk the node's arcs.
        case AtFirst{}:
          (g, +v) = gp
          Search.go(k, AtEnd{}, False{}, hf, n, h, cap, limit, stamp, size, settled, key, node, v, e, x, y, Array.get(U32, g, (node + 3 : U32)), wp)
        case AtEnd{}:
          (g, +v) = gp
          Search.go(k, AtArc{}, U32.is_lt(a, v), hf, n, h, cap, limit, stamp, size, settled, key, node, a, v, x, y, (g, 0), wp)
        case AtArc{}:
          match b:
            case True{}:
              (g, _) = gp
              Search.go(k, AtHead{}, False{}, hf, n, h, cap, limit, stamp, size, settled, key, node, a, e, x, y, Array.get(U32, g, (n + (2 * a : U32) + 4 : U32)), wp)
            case False{}:
              Search.go(k, AtNext{}, False{}, hf, n, h, cap, limit, stamp, size, settled, key, node, a, e, x, y, gp, wp)
        case AtHead{}:
          (g, +v) = gp
          Search.go(k, AtCost{}, False{}, hf, n, h, cap, limit, stamp, size, settled, key, node, a, e, v, y, Array.get(U32, g, (n + (2 * a : U32) + 5 : U32)), wp)
        case AtCost{}:
          (g, +v) = gp
          +nd = (key + v : U32)
          Search.go(k, AtNear{}, U32.is_le(nd, limit), hf, n, h, cap, limit, stamp, size, settled, key, node, a, e, x, nd, (g, 0), wp)
        case AtNear{}:
          match b:
            case True{}:
              (w, _) = wp
              Search.go(k, AtBack{}, False{}, hf, n, h, cap, limit, stamp, size, settled, key, node, a, e, x, y, gp, Relax.run(w, hf, n, h, cap, size, stamp, a, node, x, y))
            case False{}:
              +c = (a + 1 : U32)
              Search.go(k, AtArc{}, U32.is_lt(c, e), hf, n, h, cap, limit, stamp, size, settled, key, node, c, e, x, y, gp, wp)
        case AtBack{}:
          (w, +s) = wp
          Search.go(k, AtRoom{}, U32.is_eq(s, Full()), hf, n, h, cap, limit, stamp, s, settled, key, node, a, e, x, y, gp, (w, 0))
        case AtRoom{}:
          match b:
            case True{}:
              Out.make(gp, wp, settled, HeapFull{})
            case False{}:
              +c = (a + 1 : U32)
              Search.go(k, AtArc{}, U32.is_lt(c, e), hf, n, h, cap, limit, stamp, size, settled, key, node, c, e, x, y, gp, wp)

# One search from src. Costs at or under limit are exact.
def Search.run(+fuel: Nat, +hf: Nat, g: Array<U32>, w: Array<U32>, +n: U32, +cap: U32, +limit: U32, +src: U32, +stamp: U32) -> Out:
  +h = (4 * n : U32)
  w1 = Array.set(U32, Array.set(U32, w, src, 0), (n + src : U32), stamp)
  w2 = Heap.put(w1, h, 1, 0, src)
  Search.go(fuel, AtNext{}, False{}, hf, n, h, cap, limit, stamp, 1, 0, 0, 0, 0, 0, 0, 0, (g, 0), (w2, 0))

def Out.graph(o: Out) -> Array<U32>:
  match o:
    case Out{g, _, _, _}:
      g
