import Base
import ./graph.bend as G
import ./search.bend as S
import ./path.bend as P
import ./snap.bend as Sn
import ./lanes.bend as L

# The road process's IO shell. All it does is read files and hand chunks to pure
# code. Usage:
#   road bench <state folder> <searches> <limit in deciseconds> <lane depth>
#   road matrix <state folder> <points file> <output file> <limit> <lane depth>
#
# The points file holds 2 little-endian words per point: lat, lon as int32
# degrees * 1e7, like nodes.bin. The output file holds the point count, then a
# word per pair in row order: deciseconds, or 4294967295 if out of reach.

# What a state's lanes may use. The road service's cap is 1GB, and this leaves
# room for the row lists and Bend's own tables.
def Budget.bytes() -> Nat:
  900000000n

# The runtime takes at most 128 threads, so more lanes than that can't help.
def Budget.depth() -> Nat:
  7n

# Whole records, so that a chunk never ends part way through one.
def Chunk.edges() -> U32:
  786432

def Chunk.nodes() -> U32:
  786432

# Reading a file
# --------------

def Fold.got(~S: Type, ~step: List<&2, U32> -> S -> S, r: Result<&1, &1, U32 & String, List<&2, U32>>, s: S) -> S:
  match r:
    case Fail{_}:
      s
    case Done{xs}:
      step(xs, s)

def Fold.step(~S: Type, ~step: List<&2, U32> -> S -> S, pair: File & Result<&1, &1, U32 & String, List<&2, U32>>, s: S) -> File & S:
  (f, r) = pair
  (f, Fold.got(~S, ~step, r, s))

def Fold.go(~S: Type, ~step: List<&2, U32> -> S -> S, k: Nat, +size: U32, st: File & S) -> IO(File & S):
  match k:
    case 0n:
      IO.pure(File & S, st)
    case 1n+p:
      (f, s) = st
      do IO<File & S>:
        pair : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_bytes(f, size)
        out : File & S <- Fold.go(~S, ~step, p, size, Fold.step(~S, ~step, pair, s))
        return out

def Fold.close(~S: Type, st: File & S) -> IO(S):
  (f, s) = st
  do IO<S>:
    File.close(f)
    return s

def Fold.file(~S: Type, ~step: List<&2, U32> -> S -> S, +path: String, +bytes: Nat, +size: U32, s: S) -> IO(S):
  do IO<S>:
    f : File <- IO.try(File, File.open(path, "r"))
    st : File & S <- Fold.go(~S, ~step, Nat.add(Nat.div(bytes, U32.to_nat(size)), 1n), size, (f, s))
    out : S <- Fold.close(~S, st)
    return out

def Size.got(p: File & Result<&1, &1, U32 & String, U32>) -> IO(Nat):
  (f, r) = p
  do IO<Nat>:
    File.close(f)
    s : U32 <- IO.pass(U32, r)
    return U32.to_nat(s)

def Size.file(+path: String) -> IO(Nat):
  do IO<Nat>:
    f : File <- IO.try(File, File.open(path, "r"))
    p : File & Result<&1, &1, U32 & String, U32> <- File.size(f)
    s : Nat <- Size.got(p)
    return s

def Need(ok: Bool, +msg: String) -> IO(Unit):
  match ok:
    case True{}:
      IO.pure(Unit, Unit{})
    case False{}:
      IO.die(Unit, 1, msg)

# The graph
# ---------

type Loaded is Type:
  Loaded{g: Array<U32>, nodes: Nat, arcs: Nat, depth: Nat}

def Load.placed(t: G.Tally, +path: String, +nodes: Nat, +edges: Nat, +arcs: Nat) -> IO(Loaded):
  G.Tally{g, _, +seen, _, _} = t
  do IO<Loaded>:
    Need(Nat.is_eq(U32.to_nat(seen), edges), path ++ ": placed " ++ U32.show(seen) ++ " of " ++ Nat.show(edges) ++ " edges")
    return Loaded{G.Graph.head(g, U32.from_nat(nodes), U32.from_nat(arcs)), nodes, arcs, G.Size.depth(32n, False{}, G.Size.graph(nodes, edges), 0n)}

def Load.counted(t: G.Tally, +path: String, +nodes: Nat, +edges: Nat) -> IO(Loaded):
  G.Tally{g, +n, +seen, +arcs, +bad} = t
  do IO<Loaded>:
    Need(Nat.is_eq(U32.to_nat(seen), edges) && U32.is_zero(bad), path ++ ": read " ++ U32.show(seen) ++ " of " ++ Nat.show(edges) ++ " edges, " ++ U32.show(bad) ++ " bad")
    done : G.Tally <- Fold.file(~G.Tally, ~G.Place.step, path, Nat.mul(edges, 24n), Chunk.edges(), G.Tally{G.Sum.run(g, nodes), n, 0, 0, 0})
    out : Loaded <- Load.placed(done, path, nodes, edges, U32.to_nat(arcs))
    return out

def Load.graph(+folder: String) -> IO(Loaded):
  +path = folder ++ "/edges.bin"
  do IO<Loaded>:
    +raw : Nat <- Size.file(folder ++ "/nodes.bin")
    +bytes : Nat <- Size.file(path)
    +nodes : Nat = Nat.div(raw, 8n)
    +edges : Nat = Nat.div(bytes, 24n)
    t : G.Tally <- Fold.file(~G.Tally, ~G.Count.step, path, bytes, Chunk.edges(), G.Tally{[0 : U32^G.Size.depth(32n, False{}, G.Size.graph(nodes, edges), 0n)], U32.from_nat(nodes), 0, 0, 0})
    out : Loaded <- Load.counted(t, path, nodes, edges)
    return out

# Every arc pushes at most one heap entry and every entry is popped once, and
# each of those takes under 16 steps, so a search can't legitimately run out.
def Fuel.search(+nodes: Nat, +arcs: Nat) -> Nat:
  Nat.mul(Nat.add(Nat.add(nodes, arcs), 2n), 32n)

def Heap.cap(+arcs: Nat) -> Nat:
  Nat.min(Nat.add(arcs, 1n), 1048576n)

def Graph.config(+nodes: Nat, +arcs: Nat, +limit: Nat) -> L.Cfg:
  +cap = Heap.cap(arcs)
  L.Cfg{Fuel.search(nodes, arcs), 256n, nodes, U32.from_nat(nodes), U32.from_nat(cap), U32.from_nat(limit), G.Size.depth(32n, False{}, G.Size.work(nodes, cap), 0n)}

# Refuses a lane depth that doesn't fit, before any copy is made.
def Budget.check(+depth: Nat, +graph: Nat, +work: Nat) -> IO(Unit):
  +per = L.Lane.bytes(graph, work)
  +room = L.Lanes.fit(Budget.depth(), per, Budget.bytes())
  Need(Nat.is_le(per, Budget.bytes()) && Nat.is_le(depth, room), "lane depth " ++ Nat.show(depth) ++ " won't fit: a lane takes " ++ Nat.show(Nat.div(per, 1000000n)) ++ "MB and the budget allows depth " ++ Nat.show(room))

# Rows
# ----

def Rows.settled(rs: List<&2, L.Row>) -> Nat:
  match rs:
    case Nil{}:
      0n
    case +r <> t:
      Nat.add(L.Row.settled(r), Rows.settled(t))

def Rows.failed(rs: List<&2, L.Row>) -> Nat:
  match rs:
    case Nil{}:
      0n
    case +r <> t:
      Nat.add(L.Row.failed(r), Rows.failed(t))

def Rows.reached(xs: List<&2, U32>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case +x <> t:
      Nat.add(U32.to_nat(Bool.to_u32(U32.is_ne(x, L.Unreachable()))), Rows.reached(t))

def Rows.cells(rs: List<&2, L.Row>) -> Nat:
  match rs:
    case Nil{}:
      0n
    case +r <> t:
      Nat.add(Rows.reached(L.Row.cells(r)), Rows.cells(t))

def Rows.report(+lanes: Nat, +t1: Nat, +rows: List<&2, L.Row>) -> IO(Unit):
  do IO<Unit>:
    +t2 : Nat <- IO.now()
    IO.print("searches done on " ++ Nat.show(lanes) ++ " lanes, settled " ++ Nat.show(Rows.settled(rows)) ++ ", reached " ++ Nat.show(Rows.cells(rows)) ++ ", failed " ++ Nat.show(Rows.failed(rows)) ++ " in " ++ Nat.show(Nat.sub(t2, t1)) ++ "ms")
    Need(Nat.is_eq(Rows.failed(rows), 0n), "a search failed or a lookup was refused")

def Lanes.go(t: L.Lanes, +ts: List<&2, U32>, +c: L.Cfg, +lanes: Nat, +t0: Nat) -> IO(List<&2, L.Row>):
  do IO<List<&2, L.Row>>:
    +t1 : Nat <- IO.now()
    IO.print("lanes ready in " ++ Nat.show(Nat.sub(t1, t0)) ++ "ms")
    +rows : List<&2, L.Row> = L.Lanes.run(t, ts, c)
    Rows.report(lanes, t1, rows)
    return rows

# Bench
# -----

def Bench.next(+x: U32) -> U32:
  U32.mod((x * 48271 : U32), 2147483647)

def Bench.sources(k: Nat, +x: U32, +n: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match k:
    case 0n:
      List.reverse(&2, U32, acc)
    case 1n+p:
      +y = Bench.next(x)
      Bench.sources(p, y, n, U32.mod(y, n) <> acc)

def Bench.run(l: Loaded, +searches: Nat, +limit: Nat, +depth: Nat) -> IO(Unit):
  Loaded{g, +nodes, +arcs, +graph} = l
  +c = Graph.config(nodes, arcs, limit)
  +xs = Bench.sources(searches, 7919, L.Cfg.n(c), Nil{})
  do IO<Unit>:
    Budget.check(depth, graph, L.Cfg.depth(c))
    +t0 : Nat <- IO.now()
    rows : List<&2, L.Row> <- Lanes.go(L.Lanes.make(depth, g, xs), Nil{}, c, Nat.pow(2n, depth), t0)
    return Unit{}

def Bench.start(+folder: String, +searches: Nat, +limit: Nat, +depth: Nat) -> IO(Unit):
  do IO<Unit>:
    +t0 : Nat <- IO.now()
    l : Loaded <- Load.graph(folder)
    +t1 : Nat <- IO.now()
    IO.print("graph built in " ++ Nat.show(Nat.sub(t1, t0)) ++ "ms")
    Bench.run(l, searches, limit, depth)

# Matrix
# ------

type Points is Data:
  Points{lats: List<&2, U32>, lons: List<&2, U32>}

def Points.chunk(xs: List<&2, U32>, lats: List<&2, U32>, lons: List<&2, U32>) -> Points:
  match xs:
    case +a0 <> +a1 <> +a2 <> +a3 <> +b0 <> +b1 <> +b2 <> +b3 <> t:
      Points.chunk(t, G.le(a0, a1, a2, a3) <> lats, G.le(b0, b1, b2, b3) <> lons)
    case _:
      Points{lats, lons}

def Points.step(xs: List<&2, U32>, p: Points) -> Points:
  match p:
    case Points{+lats, +lons}:
      Points.chunk(xs, lats, lons)

type Snapped is Type:
  Snapped{c: Array<U32>, b: Array<U32>, nodes: List<&2, U32>, missed: Nat}

def Snap.radii() -> List<&2, U32>:
  [1, 4, 16, 64]

def Snap.got(n: Sn.Near, nodes: List<&2, U32>, +missed: Nat) -> Snapped:
  match n:
    case Sn.Near{c, b, +node, +best, _}:
      Snapped{c, b, node <> nodes, Nat.add(missed, U32.to_nat(Bool.to_u32(Nat.is_eq(best, Sn.Far()))))}

def Snap.next(s: Snapped, +lat: U32, +lon: U32) -> Snapped:
  match s:
    case Snapped{c, b, nodes, +missed}:
      Snap.got(Sn.Snap.find(Snap.radii(), c, b, lat, lon, 4294967295n), nodes, missed)

def Snap.all(lats: List<&2, U32>, lons: List<&2, U32>, s: Snapped) -> Snapped:
  match lats lons:
    case +a <> t +o <> u:
      Snap.all(t, u, Snap.next(s, a, o))
    case _ _:
      s

def Near.load(+folder: String, +nodes: Nat) -> IO(Sn.Build):
  do IO<Sn.Build>:
    s : Sn.Build <- Fold.file(~Sn.Build, ~Sn.Build.step, folder ++ "/nodes.bin", Nat.mul(nodes, 8n), Chunk.nodes(), Sn.Build{[0 : U32^G.Size.depth(32n, False{}, Nat.mul(2n, nodes), 0n)], [0 : U32^G.Size.depth(32n, False{}, Sn.Size.grid(nodes), 0n)], 0})
    return Sn.Build.place(s, nodes)

def Bytes.row(xs: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      List.reverse(&2, U32, acc)
    case +x <> t:
      Bytes.row(t, U32.shrn(x, 24n) <> U32.and(U32.shrn(x, 16n), 255) <> U32.and(U32.shrn(x, 8n), 255) <> U32.and(x, 255) <> acc)

def Written(p: File & Result<&1, &1, U32 & String, Unit>) -> IO(File):
  (f, r) = p
  match r:
    case Done{_}:
      IO.pure(File, f)
    case Fail{_}:
      IO.die(File, 1, "could not write the matrix")

def Matrix.write(rows: List<&2, L.Row>, f: File) -> IO(File):
  match rows:
    case Nil{}:
      IO.pure(File, f)
    case +r <> t:
      do IO<File>:
        p : File & Result<&1, &1, U32 & String, Unit> <- File.write_bytes(f, Bytes.row(L.Row.cells(r), Nil{}))
        f2 : File <- Written(p)
        f3 : File <- Matrix.write(t, f2)
        return f3

def Matrix.save(+path: String, +count: Nat, +rows: List<&2, L.Row>) -> IO(Unit):
  do IO<Unit>:
    f : File <- IO.try(File, File.open(path, "w"))
    p : File & Result<&1, &1, U32 & String, Unit> <- File.write_bytes(f, Bytes.row([U32.from_nat(count)], Nil{}))
    f2 : File <- Written(p)
    f3 : File <- Matrix.write(rows, f2)
    File.close(f3)

def Matrix.run(l: Loaded, +nodes: List<&2, U32>, +out: String, +limit: Nat, +depth: Nat) -> IO(Unit):
  Loaded{g, +count, +arcs, +graph} = l
  +c = Graph.config(count, arcs, limit)
  do IO<Unit>:
    Budget.check(depth, graph, L.Cfg.depth(c))
    +t0 : Nat <- IO.now()
    +rows : List<&2, L.Row> <- Lanes.go(L.Lanes.make(depth, g, nodes), nodes, c, Nat.pow(2n, depth), t0)
    Matrix.save(out, List.length(&2, U32, nodes), rows)
    +t1 : Nat <- IO.now()
    IO.print("matrix written in " ++ Nat.show(Nat.sub(t1, t0)) ++ "ms")

def Matrix.points(+path: String) -> IO(Points):
  do IO<Points>:
    +bytes : Nat <- Size.file(path)
    p : Points <- Fold.file(~Points, ~Points.step, path, bytes, Chunk.nodes(), Points{Nil{}, Nil{}})
    return p

def Matrix.snapped(s: Snapped, l: Loaded, +out: String, +limit: Nat, +depth: Nat) -> IO(Unit):
  match s:
    case Snapped{c, b, +nodes, +missed}:
      do IO<Unit>:
        Need(Nat.is_eq(missed, 0n), Nat.show(missed) ++ " points have no road nearby")
        Matrix.run(l, nodes, out, limit, depth)

def Matrix.grid(b: Sn.Build, +p: Points, l: Loaded, +out: String, +limit: Nat, +depth: Nat, +t0: Nat) -> IO(Unit):
  match b p:
    case Sn.Build{c, a, _} Points{+lats, +lons}:
      do IO<Unit>:
        s : Snapped = Snap.all(lats, lons, Snapped{c, a, Nil{}, 0n})
        +t1 : Nat <- IO.now()
        IO.print("points snapped in " ++ Nat.show(Nat.sub(t1, t0)) ++ "ms")
        Matrix.snapped(s, l, out, limit, depth)

def Matrix.loaded(l: Loaded, +folder: String, +points: String, +out: String, +limit: Nat, +depth: Nat) -> IO(Unit):
  match l:
    case Loaded{g, +nodes, +arcs, +graph}:
      do IO<Unit>:
        +t0 : Nat <- IO.now()
        b : Sn.Build <- Near.load(folder, nodes)
        +p : Points <- Matrix.points(points)
        Matrix.grid(b, p, Loaded{g, nodes, arcs, graph}, out, limit, depth, t0)

def Matrix.start(+folder: String, +points: String, +out: String, +limit: Nat, +depth: Nat) -> IO(Unit):
  do IO<Unit>:
    l : Loaded <- Load.graph(folder)
    Matrix.loaded(l, folder, points, out, limit, depth)

# Commands
# --------

def num(s: String, d: Nat) -> Nat:
  Maybe.default(&2, Nat, Nat.read(s), d)

def usage() -> IO(Unit):
  IO.print("usage: road bench <state folder> <searches> <limit in deciseconds> <lane depth>\n       road matrix <state folder> <points file> <output file> <limit> <lane depth>")

def Command.six(is_matrix: Bool, +folder: String, +a: String, +b: String, +c: String, +d: String) -> IO(Unit):
  match is_matrix:
    case True{}:
      Matrix.start(folder, a, b, num(c, 36000n), num(d, 0n))
    case False{}:
      usage()

def Command.bench(ok: Bool, +folder: String, +a: String, +b: String, +c: String) -> IO(Unit):
  match ok:
    case True{}:
      Bench.start(folder, num(a, 100n), num(b, 36000n), num(c, 0n))
    case False{}:
      usage()

def start(args: List<String>) -> IO(Unit):
  match args:
    case _ <> +cmd <> +folder <> +a <> +b <> +c <> +d <> _:
      Command.six(String.eq(cmd, "matrix"), folder, a, b, c, d)
    case _ <> +cmd <> +folder <> +a <> +b <> +c <> _:
      Command.bench(String.eq(cmd, "bench"), folder, a, b, c)
    case _:
      usage()

def main() -> IO(Unit):
  IO.bind(List<String>, Unit, IO.args(), start)
