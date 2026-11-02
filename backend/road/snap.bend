import Base
import ../core/geo.bend as Geo
import ./graph.bend as G

# Finds the road node nearest a point. Pure, like the graph build.
#
# c: coordinates, 2 words per node: lat, lon as int32 degrees * 1e7.
# b: a hash grid of 0.02 degree cells. Slot h is where bucket h's nodes start and
#    its nodes run to slot h + 1's start, numbered from Grid.first().
#
# Hashing means the grid needs no state bounds, and a collision only adds
# candidates to look at. It's built the same way as the graph: count two along,
# sum, and use the slot one along as the write position.

def Grid.buckets() -> U32:
  262144

def Grid.first() -> U32:
  262146

def Grid.cell() -> U32:
  200000

# Latitudes and longitudes as U32s, shifted so that order and division work.
def Shift.lat(+x: U32) -> U32:
  (x + 900000000 : U32)

def Shift.lon(+x: U32) -> U32:
  (x + 1800000000 : U32)

def Cell.at(+x: U32) -> U32:
  (x / Grid.cell() : U32)

def Bucket(+x: U32, +y: U32) -> U32:
  U32.and(U32.xor((x * 73856093 : U32), (y * 19349663 : U32)), (Grid.buckets() - 1 : U32))

def Size.grid(+nodes: Nat) -> Nat:
  Nat.add(nodes, U32.to_nat(Grid.first()))

# Building
# --------

type Build is Type:
  Build{c: Array<U32>, b: Array<U32>, i: U32}

# Reads one chunk of nodes.bin: stores each node and counts its bucket. Chunks
# hold whole records, and the shell compares the node total.
def Build.chunk(xs: List<&2, U32>, c: Array<U32>, b: Array<U32>, +i: U32) -> Build:
  match xs:
    case +a0 <> +a1 <> +a2 <> +a3 <> +b0 <> +b1 <> +b2 <> +b3 <> t:
      +lat = G.le(a0, a1, a2, a3)
      +lon = G.le(b0, b1, b2, b3)
      +h = Bucket(Cell.at(Shift.lon(lon)), Cell.at(Shift.lat(lat)))
      Build.chunk(t, Array.set(U32, Array.set(U32, c, (2 * i : U32), lat), ((2 * i : U32) + 1 : U32), lon), G.Count.bump(Array.get(U32, b, (h + 2 : U32)), (h + 2 : U32)), (i + 1 : U32))
    case _:
      Build{c, b, i}

def Build.step(xs: List<&2, U32>, s: Build) -> Build:
  match s:
    case Build{c, b, +i}:
      Build.chunk(xs, c, b, i)

# Turns bucket counts into positions.
def Build.sum(b: Array<U32>) -> Array<U32>:
  G.Sum.go(U32.to_nat(Grid.buckets()), 2, 0, Array.get(U32, b, 2))

def Place.put(p: Array<U32> & U32, +h: U32, +i: U32) -> Array<U32>:
  (b, +at) = p
  Array.set(U32, Array.set(U32, b, (Grid.first() + at : U32), i), (h + 1 : U32), (at + 1 : U32))

type Placing is Data:
  PlaceLat{}
  PlaceLon{}

# Puts every node in its bucket. Two steps per node.
def Place.go(k: Nat, m: Placing, +i: U32, +lat: U32, cp: Array<U32> & U32, b: Array<U32>) -> Build:
  match k:
    case 0n:
      (c, _) = cp
      Build{c, b, i}
    case 1n+f:
      match m:
        case PlaceLat{}:
          (c, +v) = cp
          Place.go(f, PlaceLon{}, i, v, Array.get(U32, c, ((2 * i : U32) + 1 : U32)), b)
        case PlaceLon{}:
          (c, +v) = cp
          +h = Bucket(Cell.at(Shift.lon(v)), Cell.at(Shift.lat(lat)))
          +j = (i + 1 : U32)
          Place.go(f, PlaceLat{}, j, 0, Array.get(U32, c, (2 * j : U32)), Place.put(Array.get(U32, b, (h + 1 : U32)), h, i))

def Build.place(s: Build, +nodes: Nat) -> Build:
  match s:
    case Build{c, b, _}:
      Place.go(Nat.mul(2n, nodes), PlaceLat{}, 0, 0, Array.get(U32, c, 0), Build.sum(b))

# Looking up
# ----------

# Further than any two points in the lower 48, squared.
def Far() -> Nat:
  Nat.mul(4294967295n, 65535n)

# Squared distance in units of 1e-5 degrees, with longitude scaled for latitude.
def Metric(+lat: U32, +lon: U32, +plat: U32, +plon: U32, +cosm: Nat) -> Nat:
  +dy = Nat.div(Geo.gap(U32.to_nat(lat), U32.to_nat(plat)), 100n)
  +dx = Nat.div(Nat.mul(Nat.div(Geo.gap(U32.to_nat(lon), U32.to_nat(plon)), 100n), cosm), 1000n)
  Nat.add(Nat.mul(dy, dy), Nat.mul(dx, dx))

# The nearest node so far, lowest number first on a tie, so that the answer never
# depends on hash order. `done` means no closer node can exist.
type Near is Type:
  Near{c: Array<U32>, b: Array<U32>, node: U32, best: Nat, done: Bool}

def word(c: Bool, +a: U32, +b: U32) -> U32:
  match c:
    case True{}:
      a
    case False{}:
      b

type Seek is Data:
  SeekCell{}
  SeekLo{}
  SeekHi{}
  SeekItem{}
  SeekNext{}
  SeekMore{}
  SeekId{}
  SeekLat{}
  SeekLon{}

def Near.made(cp: Array<U32> & U32, bp: Array<U32> & U32, +node: U32, +best: Nat) -> Near:
  (c, _) = cp
  (b, _) = bp
  Near{c, b, node, best, False{}}

# Scans the square of cells from (x, y) to (x1, y1), restarting each column at
# y0. fuel only guards termination: the shell's radii bound the square, and a
# run that used it all would just report the best node so far.
def Seek.go(k: Nat, m: Seek, f: Bool, +plat: U32, +plon: U32, +cosm: Nat, +x: U32, +y: U32, +x1: U32, +y0: U32, +y1: U32, +h: U32, +a: U32, +e: U32, +node: U32, +lat: U32, +at: U32, +best: Nat, cp: Array<U32> & U32, bp: Array<U32> & U32) -> Near:
  match k:
    case 0n:
      Near.made(cp, bp, at, best)
    case 1n+g:
      match m:
        case SeekCell{}:
          (b, _) = bp
          +c = Bucket(x, y)
          Seek.go(g, SeekLo{}, False{}, plat, plon, cosm, x, y, x1, y0, y1, c, a, e, node, lat, at, best, cp, Array.get(U32, b, c))
        case SeekLo{}:
          (b, +v) = bp
          Seek.go(g, SeekHi{}, False{}, plat, plon, cosm, x, y, x1, y0, y1, h, v, e, node, lat, at, best, cp, Array.get(U32, b, (h + 1 : U32)))
        case SeekHi{}:
          (b, +v) = bp
          Seek.go(g, SeekItem{}, U32.is_lt(a, v), plat, plon, cosm, x, y, x1, y0, y1, h, a, v, node, lat, at, best, cp, (b, 0))
        case SeekItem{}:
          match f:
            case True{}:
              (b, _) = bp
              Seek.go(g, SeekId{}, False{}, plat, plon, cosm, x, y, x1, y0, y1, h, a, e, node, lat, at, best, cp, Array.get(U32, b, (Grid.first() + a : U32)))
            case False{}:
              Seek.go(g, SeekNext{}, False{}, plat, plon, cosm, x, y, x1, y0, y1, h, a, e, node, lat, at, best, cp, bp)
        case SeekNext{}:
          +down = U32.is_lt(y, y1)
          Seek.go(g, SeekMore{}, down || U32.is_lt(x, x1), plat, plon, cosm, word(down, x, (x + 1 : U32)), word(down, (y + 1 : U32), y0), x1, y0, y1, h, a, e, node, lat, at, best, cp, bp)
        case SeekMore{}:
          match f:
            case True{}:
              Seek.go(g, SeekCell{}, False{}, plat, plon, cosm, x, y, x1, y0, y1, h, a, e, node, lat, at, best, cp, bp)
            case False{}:
              Near.made(cp, bp, at, best)
        case SeekId{}:
          (c, _) = cp
          (b, +v) = bp
          Seek.go(g, SeekLat{}, False{}, plat, plon, cosm, x, y, x1, y0, y1, h, a, e, v, lat, at, best, Array.get(U32, c, (2 * v : U32)), (b, 0))
        case SeekLat{}:
          (c, +v) = cp
          Seek.go(g, SeekLon{}, False{}, plat, plon, cosm, x, y, x1, y0, y1, h, a, e, node, v, at, best, Array.get(U32, c, ((2 * node : U32) + 1 : U32)), bp)
        case SeekLon{}:
          (c, +v) = cp
          +d = Metric(Shift.lat(lat), Shift.lon(v), plat, plon, cosm)
          +b2 = (a + 1 : U32)
          +wins = Nat.is_lt(d, best) || (Nat.is_eq(d, best) && U32.is_lt(node, at))
          Seek.go(g, SeekItem{}, U32.is_lt(b2, e), plat, plon, cosm, x, y, x1, y0, y1, h, b2, e, node, lat, word(wins, node, at), Nat.min(d, best), (c, 0), bp)

# Whether every node outside a square of this radius is further than `best`: the
# point is at least radius cells from the square's edge, and a cell is 2000 units
# high and at least 2000 * cos(lat) wide.
def Snap.sure(+best: Nat, +r: U32, +cosm: Nat) -> Bool:
  +safe = Nat.div(Nat.mul(Nat.mul(U32.to_nat(r), 2000n), cosm), 1000n)
  Nat.is_le(best, Nat.mul(safe, safe))

def Snap.scanned(n: Near, +r: U32, +cosm: Nat) -> Near:
  match n:
    case Near{c, b, +node, +best, _}:
      Near{c, b, node, best, Snap.sure(best, r, cosm)}

def Snap.round(done: Bool, c: Array<U32>, b: Array<U32>, +node: U32, +best: Nat, +r: U32, +plat: U32, +plon: U32, +cosm: Nat, +fuel: Nat) -> Near:
  match done:
    case True{}:
      Near{c, b, node, best, True{}}
    case False{}:
      +x = Cell.at(plon)
      +y = Cell.at(plat)
      Snap.scanned(Seek.go(fuel, SeekCell{}, False{}, plat, plon, cosm, (x - r : U32), (y - r : U32), (x + r : U32), (y - r : U32), (y + r : U32), 0, 0, 0, 0, 0, node, best, (c, 0), (b, 0)), r, cosm)

def Snap.try(rs: List<&2, U32>, s: Near, +plat: U32, +plon: U32, +cosm: Nat, +fuel: Nat) -> Near:
  match rs:
    case Nil{}:
      s
    case +r <> t:
      match s:
        case Near{c, b, +node, +best, done}:
          Snap.try(t, Snap.round(done, c, b, node, best, r, plat, plon, cosm, fuel), plat, plon, cosm, fuel)

# The nearest node to a point given as int32 degrees * 1e7. best stays at Far()
# if there's no road within about 140km.
def Snap.find(+rs: List<&2, U32>, c: Array<U32>, b: Array<U32>, +lat: U32, +lon: U32, +fuel: Nat) -> Near:
  +cosm = Geo.cos_milli(Nat.div(Nat.sub(U32.to_nat(Shift.lat(lat)), 900000000n), 10000000n))
  Snap.try(rs, Near{c, b, 0, Far(), False{}}, Shift.lat(lat), Shift.lon(lon), cosm, fuel)
