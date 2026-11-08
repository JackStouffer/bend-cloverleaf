import Base
import ./types.bend as T
import ./geo.bend as Geo

# Drive minutes between points, from the road process's travel-time matrices.
# Each state's table is Data, so every lane can read it, and it's a search tree
# keyed by coordinates, so the core still asks for the time from one Point to
# another. No law looks inside these numbers.
#
# The road search stops at a limit, so a pair can be missing because it's
# further than that or because no road joins it. Either way the time is at least
# the limit, so a missing pair takes the straight-line estimate, but never less
# than `floor`. With no table at all, every time is the straight-line estimate.

type Entry is Data:
  Entry{from: T.Point, to: T.Point, minutes: Nat}


# Longitudes stay under 2^21 in the lower 48, so this is one Nat per point.
def Point.key(+p: T.Point) -> Nat:
  Nat.add(Nat.mul(T.Point.lat(p), 2097152n), T.Point.lon(p))

def none() -> T.Times:
  T.Times{0n, 0n, T.STip{}}

# Looking up
# ----------

def Maybe.hit(c: Bool, +m: Nat, found: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match c:
    case True{}:
      Some{m}
    case False{}:
      found

def Row.pick(c: Bool, l: T.Row, r: T.Row) -> T.Row:
  match c:
    case True{}:
      l
    case False{}:
      r

def Rows.pick(c: Bool, l: T.Rows, r: T.Rows) -> T.Rows:
  match c:
    case True{}:
      l
    case False{}:
      r

def Row.hit(c: Bool, row: T.Row, found: T.Row) -> T.Row:
  match c:
    case True{}:
      row
    case False{}:
      found

# Tail calls with the answer carried along, so each walk is a flat loop.
def Row.find(fuel: Nat, row: T.Row, +k: Nat, found: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match fuel:
    case 0n:
      found
    case 1n+f:
      match row:
        case T.RTip{}:
          found
        case T.RBin{+key, +m, l, r}:
          Row.find(f, Row.pick(Nat.is_lt(k, key), l, r), k, Maybe.hit(Nat.is_eq(k, key), m, found))

def Rows.find(fuel: Nat, rows: T.Rows, +k: Nat, found: T.Row) -> T.Row:
  match fuel:
    case 0n:
      found
    case 1n+f:
      match rows:
        case T.STip{}:
          found
        case T.SBin{+key, +row, l, r}:
          Rows.find(f, Rows.pick(Nat.is_lt(k, key), l, r), k, Row.hit(Nat.is_eq(k, key), row, found))

def minutes.missing(m: Maybe<&2, Nat>, +floor: Nat, +a: T.Point, +b: T.Point) -> Nat:
  match m:
    case Some{x}:
      x
    case None{}:
      Nat.max(Geo.minutes(a, b), floor)

def minutes.go(same: Bool, t: T.Times, +a: T.Point, +b: T.Point) -> Nat:
  match same:
    case True{}:
      0n
    case False{}:
      match t:
        case T.Times{+floor, +depth, rows}:
          +row = Rows.find(depth, rows, Point.key(a), T.RTip{})
          minutes.missing(Row.find(depth, row, Point.key(b), None{}), floor, a, b)

# Drive minutes from a to b.
def minutes(+t: T.Times, +a: T.Point, +b: T.Point) -> Nat:
  minutes.go(T.Point.is_eq(a, b), t, a, b)

# Building
# --------

type Cell is Data:
  Cell{a: Nat, b: Nat, m: Nat}

type Line is Data:
  Line{a: Nat, size: Nat, cells: List<&2, Cell>}

def Cell.a(c: Cell) -> Nat:
  match c:
    case Cell{a, b, m}:
      a

def Cell.b(c: Cell) -> Nat:
  match c:
    case Cell{a, b, m}:
      b

def Cell.m(c: Cell) -> Nat:
  match c:
    case Cell{a, b, m}:
      m

def Cell.le(x: Cell, y: Cell) -> Bool:
  match x y:
    case Cell{+a1, +b1, _} Cell{+a2, +b2, _}:
      Bool.or(Nat.is_lt(a1, a2), Bool.and(Nat.is_eq(a1, a2), Nat.is_le(b1, b2)))

def Entry.cell(e: Entry) -> Cell:
  match e:
    case Entry{+f, +t, m}:
      Cell{Point.key(f), Point.key(t), m}

def cells(es: List<&2, Entry>, acc: List<&2, Cell>) -> List<&2, Cell>:
  match es:
    case Nil{}:
      acc
    case e <> t:
      cells(t, Entry.cell(e) <> acc)

def Line.put(c: Bool, +x: Cell, +l: Line, rest: List<&2, Line>) -> List<&2, Line>:
  match c:
    case True{}:
      match l:
        case Line{a, n, cs}:
          Line{a, 1n+n, x <> cs} <> rest
    case False{}:
      Line{Cell.a(x), 1n, [x]} <> l <> rest

def Line.open(+x: Cell, acc: List<&2, Line>) -> List<&2, Line>:
  match acc:
    case Nil{}:
      [Line{Cell.a(x), 1n, [x]}]
    case +l <> rest:
      match l:
        case Line{+a, _, _}:
          Line.put(Nat.is_eq(a, Cell.a(x)), x, l, rest)

# Sorted cells into lines, one per source point. Both come out reversed.
def group(xs: List<&2, Cell>, acc: List<&2, Line>) -> List<&2, Line>:
  match xs:
    case Nil{}:
      acc
    case +x <> t:
      group(t, Line.open(x, acc))

def Row.split(xs: List<&2, Cell>, k: Cell -> List<&2, Cell> -> T.Row) -> T.Row:
  match xs:
    case Nil{}:
      T.RTip{}
    case c <> t:
      k(c, t)

# A balanced tree from cells sorted by destination.
def Row.of(fuel: Nat, +size: Nat, +xs: List<&2, Cell>) -> T.Row:
  match fuel:
    case 0n:
      T.RTip{}
    case 1n+f:
      +g = f
      +half = Nat.div(size, 2n)
      Row.split(List.drop(&2, Cell, xs, half),
        +c => t => T.RBin{Cell.b(c), Cell.m(c), Row.of(g, half, List.take(&2, Cell, xs, half)), Row.of(g, Nat.sub(size, Nat.add(half, 1n)), t)})

def Line.row(+fuel: Nat, l: Line) -> T.Row:
  match l:
    case Line{a, n, cs}:
      Row.of(fuel, n, List.reverse(&2, Cell, cs))

def Line.a(l: Line) -> Nat:
  match l:
    case Line{a, n, cs}:
      a

def Rows.split(xs: List<&2, Line>, k: Line -> List<&2, Line> -> T.Rows) -> T.Rows:
  match xs:
    case Nil{}:
      T.STip{}
    case l <> t:
      k(l, t)

def Rows.of(fuel: Nat, +depth: Nat, +size: Nat, +xs: List<&2, Line>) -> T.Rows:
  match fuel:
    case 0n:
      T.STip{}
    case 1n+f:
      +g = f
      +half = Nat.div(size, 2n)
      Rows.split(List.drop(&2, Line, xs, half),
        +l => t => T.SBin{Line.a(l), Line.row(depth, l), Rows.of(g, depth, half, List.take(&2, Line, xs, half)), Rows.of(g, depth, Nat.sub(size, Nat.add(half, 1n)), t)})

def of.lines(+floor: Nat, +depth: Nat, +lines: List<&2, Line>) -> T.Times:
  T.Times{floor, depth, Rows.of(depth, depth, List.length(&2, Line, lines), lines)}

# A table from cells keyed by Point.key, in any order.
def of.cells(+floor: Nat, cs: List<&2, Cell>) -> T.Times:
  +sorted = List.sort(~Cell, ~Cell.le, cs)
  of.lines(floor, 48n, List.reverse(&2, Line, group(sorted, Nil{})))

# A table from any list of entries, in any order. Where a pair appears twice,
# the lookup finds one of them.
def of(+floor: Nat, es: List<&2, Entry>) -> T.Times:
  of.cells(floor, cells(es, Nil{}))
