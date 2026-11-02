import Base

# Builds one state's adjacency from its edge records. Pure: the shell hands in
# chunks of edges.bin, and nothing here sees a file.
#
# An edge is 6 little-endian words: from, to, meters, deciseconds, flags, shape.
# Bit 4 of flags means one-way, so any other edge becomes two arcs.
#
# The result is the graph that road/search.bend reads: g[0] nodes, g[1] arcs,
# first arc per node from slot 2, then arcs from slot n + 4 as (head,
# deciseconds). A node's arcs run up to the next node's first arc.
#
# It's built in place in three steps. Count each node's arcs two slots along,
# sum them, and then use the slot one along as the node's write position. Each
# write position ends on where the next node starts, which is the finished table.

def Edge.bytes() -> U32:
  24

def Edge.one_way() -> U32:
  16

def Node.bytes() -> U32:
  8

def le(+a: U32, +b: U32, +c: U32, +d: U32) -> U32:
  U32.or(a, U32.or(U32.shln(b, 8n), U32.or(U32.shln(c, 16n), U32.shln(d, 24n))))

# Sizes
# -----

# The smallest depth whose array holds this many words. fuel only guards
# termination, since a U32 index can only reach depth 32.
def Size.depth(fuel: Nat, fits: Bool, +words: Nat, +d: Nat) -> Nat:
  match fuel:
    case 0n:
      d
    case 1n+f:
      match fits:
        case True{}:
          d
        case False{}:
          Size.depth(f, Nat.is_le(words, Nat.pow(2n, 1n+d)), words, 1n+d)

# The arc count isn't known before the first pass, so this is the bound: every
# edge is two-way.
def Size.graph(+nodes: Nat, +edges: Nat) -> Nat:
  Nat.add(Nat.add(nodes, 4n), Nat.mul(4n, edges))

def Size.work(+nodes: Nat, +cap: Nat) -> Nat:
  Nat.add(Nat.mul(4n, nodes), Nat.mul(2n, Nat.add(cap, 2n)))

# Reading edges
# -------------

# What a pass over the edge records has seen so far. `bad` counts edges naming a
# node past the end, which would wrap and corrupt the table without failing.
type Tally is Type:
  Tally{g: Array<U32>, n: U32, edges: U32, arcs: U32, bad: U32}

def Count.bump(p: Array<U32> & U32, +i: U32) -> Array<U32>:
  (a, +v) = p
  Array.set(U32, a, i, (v + 1 : U32))

def Count.one(a: Array<U32>, +i: U32) -> Array<U32>:
  Count.bump(Array.get(U32, a, (i + 4 : U32)), (i + 4 : U32))

def Count.ends(two: Bool, g: Array<U32>, +from: U32, +to: U32) -> Array<U32>:
  match two:
    case True{}:
      Count.one(Count.one(g, from), to)
    case False{}:
      Count.one(g, from)

def Count.edge(ok: Bool, two: Bool, g: Array<U32>, +from: U32, +to: U32) -> Array<U32>:
  match ok:
    case True{}:
      Count.ends(two, g, from, to)
    case False{}:
      g

def Edge.two(+flags: U32) -> Bool:
  U32.is_zero(U32.and(flags, Edge.one_way()))

def Edge.fits(+n: U32, +from: U32, +to: U32) -> Bool:
  U32.is_lt(from, n) && U32.is_lt(to, n)

# The first pass over one chunk. A chunk that ends part way through a record
# leaves that record uncounted, and the shell compares the edge total.
def Count.chunk(xs: List<&2, U32>, g: Array<U32>, +n: U32, +edges: U32, +arcs: U32, +bad: U32) -> Tally:
  match xs:
    case +a0 <> +a1 <> +a2 <> +a3 <> +b0 <> +b1 <> +b2 <> +b3 <> _ <> _ <> _ <> _ <> _ <> _ <> _ <> _ <> +f0 <> _ <> _ <> _ <> _ <> _ <> _ <> _ <> t:
      +from = le(a0, a1, a2, a3)
      +to = le(b0, b1, b2, b3)
      +ok = Edge.fits(n, from, to)
      +two = Edge.two(f0)
      Count.chunk(t, Count.edge(ok, two, g, from, to), n, (edges + 1 : U32), (arcs + 1 + Bool.to_u32(two) : U32), (bad + Bool.to_u32(Bool.not(ok)) : U32))
    case _:
      Tally{g, n, edges, arcs, bad}

# Turns counts into positions: each slot becomes the sum of those up to it.
def Sum.go(k: Nat, +i: U32, +acc: U32, p: Array<U32> & U32) -> Array<U32>:
  match k:
    case 0n:
      (a, _) = p
      a
    case 1n+f:
      (a, +v) = p
      +s = (acc + v : U32)
      +j = (i + 1 : U32)
      Sum.go(f, j, s, Array.get(U32, Array.set(U32, a, i, s), j))

def Sum.run(g: Array<U32>, +nodes: Nat) -> Array<U32>:
  Sum.go(nodes, 4, 0, Array.get(U32, g, 4))

def Place.at(p: Array<U32> & U32, +n: U32, +from: U32, +to: U32, +cost: U32) -> Array<U32>:
  (g, +i) = p
  +at = (n + (2 * i : U32) + 4 : U32)
  Array.set(U32, Array.set(U32, Array.set(U32, g, at, to), (at + 1 : U32), cost), (from + 3 : U32), (i + 1 : U32))

def Place.arc(g: Array<U32>, +n: U32, +from: U32, +to: U32, +cost: U32) -> Array<U32>:
  Place.at(Array.get(U32, g, (from + 3 : U32)), n, from, to, cost)

def Place.ends(two: Bool, g: Array<U32>, +n: U32, +from: U32, +to: U32, +cost: U32) -> Array<U32>:
  match two:
    case True{}:
      Place.arc(Place.arc(g, n, from, to, cost), n, to, from, cost)
    case False{}:
      Place.arc(g, n, from, to, cost)

# The second pass. A bad edge stops the build before this pass runs.
def Place.chunk(xs: List<&2, U32>, g: Array<U32>, +n: U32, +edges: U32) -> Tally:
  match xs:
    case +a0 <> +a1 <> +a2 <> +a3 <> +b0 <> +b1 <> +b2 <> +b3 <> _ <> _ <> _ <> _ <> +c0 <> +c1 <> +c2 <> +c3 <> +f0 <> _ <> _ <> _ <> _ <> _ <> _ <> _ <> t:
      Place.chunk(t, Place.ends(Edge.two(f0), g, n, le(a0, a1, a2, a3), le(b0, b1, b2, b3), le(c0, c1, c2, c3)), n, (edges + 1 : U32))
    case _:
      Tally{g, n, edges, 0, 0}

def Count.step(xs: List<&2, U32>, t: Tally) -> Tally:
  match t:
    case Tally{g, +n, +edges, +arcs, +bad}:
      Count.chunk(xs, g, n, edges, arcs, bad)

def Place.step(xs: List<&2, U32>, t: Tally) -> Tally:
  match t:
    case Tally{g, +n, +edges, _, _}:
      Place.chunk(xs, g, n, edges)

def Graph.head(g: Array<U32>, +n: U32, +arcs: U32) -> Array<U32>:
  Array.set(U32, Array.set(U32, g, 0, n), 1, arcs)
