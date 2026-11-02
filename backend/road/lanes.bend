import Base
import ./search.bend as S
import ./path.bend as P

# Search lanes. An array has one owner, so each lane needs its own copy of the
# graph. Copies are made once, before any fork, and then each lane runs on its
# own until its work is done.
#
# The scheduler decides how to run a fork from the def the task runs. A def that
# can fork is run while the tree is still growing, on only a couple of threads,
# so a lane has to be a parallel call to a def that never forks. Calling it from
# inside a forking def's own base case leaves half the lanes waiting.
#
# Work is dealt out one by one, not cut into runs, because sources arrive in
# geographic order and tasks are never moved once assigned: a lane holding all
# of a city's stops would finish long after its neighbours.

def Deal.put(-A: Data, +h: A, p: List<&2, A> & List<&2, A>) -> List<&2, A> & List<&2, A>:
  (a, b) = p
  (h <> b, a)

# Odd positions, then even ones.
def Deal.split(-A: Data, xs: List<&2, A>) -> List<&2, A> & List<&2, A>:
  match xs:
    case Nil{}:
      (Nil{}, Nil{})
    case +h <> t:
      Deal.put(A, h, Deal.split(A, t))

# Puts dealt lists back in their original order.
def Deal.merge(-A: Data, xs: List<&2, A>, ys: List<&2, A>) -> List<&2, A>:
  match xs ys:
    case Nil{} _:
      ys
    case _ Nil{}:
      xs
    case +a <> s +b <> t:
      a <> b <> Deal.merge(A, s, t)

def Deal.undo(-A: Data, p: List<&2, A> & List<&2, A>) -> List<&2, A>:
  (a, b) = p
  Deal.merge(A, a, b)

# Search settings that every lane reads: search and heap fuel, node count as a
# Nat and a U32, heap capacity, limit in deciseconds, and the workspace depth.
type Cfg is Data:
  Cfg{fuel: Nat, sink: Nat, nodes: Nat, n: U32, cap: U32, limit: U32, depth: Nat}

def Cfg.fuel(+c: Cfg) -> Nat:
  match c:
    case Cfg{+x, _, _, _, _, _, _}:
      x

def Cfg.sink(+c: Cfg) -> Nat:
  match c:
    case Cfg{_, +x, _, _, _, _, _}:
      x

def Cfg.nodes(+c: Cfg) -> Nat:
  match c:
    case Cfg{_, _, +x, _, _, _, _}:
      x

def Cfg.n(+c: Cfg) -> U32:
  match c:
    case Cfg{_, _, _, +x, _, _, _}:
      x

def Cfg.cap(+c: Cfg) -> U32:
  match c:
    case Cfg{_, _, _, _, +x, _, _}:
      x

def Cfg.limit(+c: Cfg) -> U32:
  match c:
    case Cfg{_, _, _, _, _, +x, _}:
      x

def Cfg.depth(+c: Cfg) -> Nat:
  match c:
    case Cfg{_, _, _, _, _, _, +x}:
      x

# One row
# -------

def Unreachable() -> U32:
  4294967295

def Cell.code(+c: Maybe<&2, Nat>) -> U32:
  match c:
    case None{}:
      Unreachable()
    case Some{+t}:
      U32.from_nat(t)

type Scan is Type:
  Scan{g: Array<U32>, w: Array<U32>, cells: List<&2, U32>, refused: Nat}

def Scan.got(c: P.Cell, cells: List<&2, U32>, +refused: Nat) -> Scan:
  match c:
    case P.Cell{g, w, _, +cost, bad}:
      Scan{g, w, Cell.code(cost) <> cells, Nat.add(refused, U32.to_nat(Bool.to_u32(bad)))}

def Scan.one(s: Scan, +c: Cfg, +src: U32, +dst: U32, +stamp: U32) -> Scan:
  match s:
    case Scan{g, w, cells, +refused}:
      Scan.got(P.Cell.read(g, w, Nat.mul(3n, Cfg.nodes(c)), Cfg.n(c), Cfg.limit(c), src, dst, stamp), cells, refused)

def Scan.go(ts: List<&2, U32>, s: Scan, +c: Cfg, +src: U32, +stamp: U32) -> Scan:
  match ts:
    case Nil{}:
      s
    case +dst <> t:
      Scan.go(t, Scan.one(s, c, src, dst, stamp), c, src, stamp)

# One source's drive times, in target order, and what its search cost. A failed
# search or a refused lookup leaves `failed` above zero, and the shell won't
# report such a batch.
type Row is Data:
  Row{cells: List<&2, U32>, settled: Nat, failed: Nat}

def Row.cells(+r: Row) -> List<&2, U32>:
  match r:
    case Row{+x, _, _}:
      x

def Row.settled(+r: Row) -> Nat:
  match r:
    case Row{_, +x, _}:
      x

def Row.failed(+r: Row) -> Nat:
  match r:
    case Row{_, _, +x}:
      x

type Sweep is Type:
  Sweep{g: Array<U32>, w: Array<U32>, rows: List<&2, Row>}

def Sweep.scanned(s: Scan, rows: List<&2, Row>, +settled: Nat) -> Sweep:
  match s:
    case Scan{g, w, +cells, +refused}:
      Sweep{g, w, Row{List.reverse(&2, U32, cells), settled, refused} <> rows}

def Sweep.searched(ok: Bool, g: Array<U32>, w: Array<U32>, rows: List<&2, Row>, +ts: List<&2, U32>, +c: Cfg, +src: U32, +stamp: U32, +settled: Nat) -> Sweep:
  match ok:
    case True{}:
      Sweep.scanned(Scan.go(ts, Scan{g, w, Nil{}, 0n}, c, src, stamp), rows, settled)
    case False{}:
      Sweep{g, w, Row{Nil{}, settled, 1n} <> rows}

def Why.finished(+w: S.Why) -> Bool:
  match w:
    case S.Finished{}:
      True{}
    case _:
      False{}

def Sweep.out(o: S.Out, rows: List<&2, Row>, +ts: List<&2, U32>, +c: Cfg, +src: U32, +stamp: U32) -> Sweep:
  match o:
    case S.Out{g, w, +settled, +why}:
      Sweep.searched(Why.finished(why), g, w, rows, ts, c, src, stamp, U32.to_nat(settled))

def Sweep.one(s: Sweep, +ts: List<&2, U32>, +c: Cfg, +src: U32, +stamp: U32) -> Sweep:
  match s:
    case Sweep{g, w, rows}:
      Sweep.out(S.Search.run(Cfg.fuel(c), Cfg.sink(c), g, w, Cfg.n(c), Cfg.cap(c), Cfg.limit(c), src, stamp), rows, ts, c, src, stamp)

def Sweep.go(xs: List<&2, U32>, s: Sweep, +ts: List<&2, U32>, +c: Cfg, +stamp: U32) -> Sweep:
  match xs:
    case Nil{}:
      s
    case +src <> t:
      Sweep.go(t, Sweep.one(s, ts, c, src, stamp), ts, c, (stamp + 1 : U32))

def Sweep.rows(s: Sweep) -> List<&2, Row>:
  match s:
    case Sweep{_, _, rows}:
      List.reverse(&2, Row, rows)

# A lane: its own graph and workspace, one row per source. Every fork below ends
# in a parallel call to this def, which never forks.
def Lane.run(g: Array<U32>, xs: List<&2, U32>, +ts: List<&2, U32>, +c: Cfg) -> List<&2, Row>:
  Sweep.rows(Sweep.go(xs, Sweep{g, [0 : U32^Cfg.depth(c)], Nil{}}, ts, c, 1))

# Lanes
# -----

# Bytes one lane costs: its copy of the graph and its workspace, at 4 bytes a
# word, from their array depths.
def Lane.bytes(+graph: Nat, +work: Nat) -> Nat:
  Nat.mul(4n, Nat.add(Nat.pow(2n, graph), Nat.pow(2n, work)))

# The deepest lane tree whose lanes all fit in the budget. Bend has no heap limit,
# so going over gets the process or the whole machine killed with no error, and
# the shell checks a request against this before it makes a single copy. fuel
# bounds the depth, so no request can reach a number that overflows.
def Lanes.room(k: Nat, fits: Bool, +lanes: Nat, +per: Nat, +budget: Nat, +d: Nat) -> Nat:
  match k:
    case 0n:
      d
    case 1n+f:
      match fits:
        case True{}:
          +next = Nat.mul(2n, lanes)
          Lanes.room(f, Nat.is_le(Nat.mul(Nat.mul(2n, next), per), budget), next, per, budget, 1n+d)
        case False{}:
          d

def Lanes.fit(+k: Nat, +per: Nat, +budget: Nat) -> Nat:
  Lanes.room(k, Nat.is_le(Nat.mul(Nat.mul(2n, 1n), per), budget), 1n, per, budget, 0n)

type Lanes is Type:
  One{g: Array<U32>, jobs: List<&2, U32>}
  Two{l: Lanes, r: Lanes}

# 2^(d + 1) lanes from a graph and its copy.
def Lanes.grow(+d: Nat, gs: Array<U32> & Array<U32>, xs: List<&2, U32> & List<&2, U32>) -> Lanes:
  match d:
    case 0n:
      (a, b) = gs
      (x, y) = xs
      Two{One{a, x}, One{b, y}}
    case 1n+e:
      (a, b) = gs
      (x, y) = xs
      Two{Lanes.grow(e, Array.clone(U32, a), Deal.split(U32, x)), Lanes.grow(e, Array.clone(U32, b), Deal.split(U32, y))}

# 2^d lanes.
def Lanes.make(+d: Nat, g: Array<U32>, xs: List<&2, U32>) -> Lanes:
  match d:
    case 0n:
      One{g, xs}
    case 1n+e:
      Lanes.grow(e, Array.clone(U32, g), Deal.split(U32, xs))

# Rows in the order the sources came in.
def Lanes.run(t: Lanes, +ts: List<&2, U32>, +c: Cfg) -> List<&2, Row>:
  match t:
    case One{g, xs}:
      Lane.run(g, xs, ts, c)
    case Two{One{g, xs}, One{h, ys}}:
      a b = Lane.run(g, xs, ts, c) Lane.run(h, ys, ts, c)
      Deal.merge(Row, a, b)
    case Two{l, r}:
      a b = Lanes.run(l, ts, c) Lanes.run(r, ts, c)
      Deal.merge(Row, a, b)
