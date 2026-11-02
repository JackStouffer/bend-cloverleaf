import Base
import ../core/types.bend as T
import ../core/lifecycle.bend as Life
import ../core/jobs.bend as J
import ../core/route.bend as R
import ../core/plan.bend as P
import ../core/heal.bend as H
import ../core/solve.bend as S
import ../core/geo.bend as Geo
import ../solver/synth.bend as Syn
import ../road/graph.bend as RG
import ../road/search.bend as RS
import ../road/path.bend as RP
import ../road/snap.bend as RN
import ../road/lanes.bend as RL

# Concrete runs through the core. The laws say what must always hold, and this
# says the code does the useful thing on real numbers, which they don't cover.

type Check is Data:
  Check{name: String, ok: Bool}

def between(+x: Nat, +lo: Nat, +hi: Nat) -> Bool:
  Bool.and(Nat.is_ge(x, lo), Nat.is_le(x, hi))

def nyc() -> T.Point:
  T.Point{407128n, 740060n}

def la() -> T.Point:
  T.Point{340522n, 1182437n}

def chicago() -> T.Point:
  T.Point{418781n, 876298n}

def houston() -> T.Point:
  T.Point{297604n, 953698n}

def near_nyc(+north: Nat) -> T.Point:
  T.Point{Nat.add(407128n, north), 740060n}

# New York's FIPS code. Every scenario runs in one state, like any real instance.
def ny() -> Nat:
  36n

def job(+id: Nat, +north: Nat, +zip: Nat, +due: Nat) -> T.Appraisal:
  T.Appraisal{id, near_nyc(north), zip, due, 20n, ny()}

def crew(+id: Nat, +zips: List<&2, Nat>, +max: Nat) -> T.Contractor:
  T.Contractor{id, nyc(), zips, max, [10n, 11n], ny()}

def inst() -> T.Instance:
  T.Instance{[crew(1n, [100n, 101n], 480n), crew(2n, [102n], 480n)],
    [job(1n, 100n, 100n, 10n), job(2n, 200n, 100n, 10n), job(3n, 300n, 101n, 11n), job(4n, 400n, 102n, 10n)], 60n, ny()}

# Georgia's FIPS code, for anything that belongs to another state's instance.
def foreign_job() -> T.Appraisal:
  T.Appraisal{9n, near_nyc(100n), 100n, 10n, 20n, 13n}

def foreign_crew() -> T.Instance:
  T.Instance{[T.Contractor{1n, nyc(), [100n], 480n, [10n], 13n}], [job(1n, 100n, 100n, 10n)], 60n, ny()}

def foreign_jobs() -> T.Instance:
  T.Instance{[crew(1n, [100n], 480n)], [foreign_job()], 60n, ny()}

def tune() -> S.Tuning:
  S.Tuning.standard()

def solved() -> T.Plan:
  S.solve(tune(), inst(), 10n, 12n)

def start() -> H.State:
  H.State{inst(), solved()}

def valid(+st: H.State) -> Bool:
  P.Plan.valid(H.State.inst(st), H.State.plan(st))

def count_routes(routes: List<&2, T.Route>) -> Nat:
  match routes:
    case Nil{}:
      0n
    case +r <> t:
      Nat.add(List.length(&2, T.Stop, T.Route.stops(r)), count_routes(t))

def on_routes(+st: H.State) -> Nat:
  count_routes(T.Plan.routes(H.State.plan(st)))

def backlog(+st: H.State) -> Nat:
  List.length(&2, T.Appraisal, T.Plan.backlog(H.State.plan(st)))

def placed(+st: H.State) -> Nat:
  List.length(&2, T.Appraisal, P.Plan.placed(H.State.plan(st)))

def id_placed(+st: H.State, +i: Nat) -> Bool:
  J.has_id(P.Plan.placed(H.State.plan(st)), i)

def first_open.pick(xs: List<&2, T.Stop>, r: Nat) -> Nat:
  match xs:
    case Nil{}:
      r
    case s <> t:
      T.Stop.id(s)

# The first open stop on the first route with work.
def first_open(routes: List<&2, T.Route>) -> Nat:
  match routes:
    case Nil{}:
      0n
    case +r <> t:
      first_open.pick(H.Route.t(r), first_open(t))

def next_id(+st: H.State) -> Nat:
  first_open(T.Plan.routes(H.State.plan(st)))

def after(+st: H.State, ev: H.Change) -> H.State:
  H.Heal.apply(st, ev)

def progress(+st: H.State, ev: H.Progress) -> H.State:
  H.Progress.apply(st, ev)

def far_job() -> T.Appraisal:
  job(9n, 50n, 900n, 11n)

# A crew limited to a short day, to see the planner stop at its hours.
def short_inst() -> T.Instance:
  T.Instance{[crew(1n, [100n], 60n)], [job(1n, 100n, 100n, 20n), job(2n, 200n, 100n, 20n), job(3n, 300n, 100n, 20n), job(4n, 400n, 100n, 20n),
    job(5n, 500n, 100n, 20n), job(6n, 600n, 100n, 20n), job(7n, 700n, 100n, 20n), job(8n, 800n, 100n, 20n)], 60n, ny()}

# One day with room for about two stops, and the job due first listed last.
def tight_inst() -> T.Instance:
  T.Instance{[crew(1n, [100n], 60n)], [job(1n, 100n, 100n, 30n), job(2n, 200n, 100n, 30n), job(3n, 300n, 100n, 30n), job(4n, 400n, 100n, 10n)], 60n, ny()}

# Work nobody covers, due inside the horizon: it should cross a zip and be flagged.
def outside_inst() -> T.Instance:
  T.Instance{[crew(1n, [100n], 480n)], [job(1n, 100n, 555n, 10n)], 60n, ny()}

# Same, but too far for the cap.
def too_far_inst() -> T.Instance:
  T.Instance{[crew(1n, [100n], 2000n)], [T.Appraisal{1n, la(), 555n, 10n, 20n, ny()}], 60n, ny()}

def total_outside(routes: List<&2, T.Route>) -> Nat:
  match routes:
    case Nil{}:
      0n
    case +r <> t:
      Nat.add(List.length(&2, Nat, T.Audit.outside(T.Route.audit(r))), total_outside(t))

def total_late(routes: List<&2, T.Route>) -> Nat:
  match routes:
    case Nil{}:
      0n
    case +r <> t:
      Nat.add(List.length(&2, Nat, T.Audit.late(T.Route.audit(r))), total_late(t))

def overtime(routes: List<&2, T.Route>) -> Nat:
  match routes:
    case Nil{}:
      0n
    case +r <> t:
      Nat.add(U32.to_nat(Bool.to_u32(T.Audit.overtime(T.Route.audit(r)))), overtime(t))

def exceptions(+p: T.Plan) -> Nat:
  List.length(&2, T.Exception, T.Plan.exceptions(p))

def waiting(+p: T.Plan) -> Nat:
  List.length(&2, T.Appraisal, T.Plan.backlog(p))

def bench() -> T.Instance:
  Syn.instance(40n, 400n, 20000n, 5n)

def bench_plan() -> T.Plan:
  S.solve(tune(), bench(), 20000n, 20005n)

def geo_checks() -> List<&2, Check>:
  [Check{"same point is zero minutes", Nat.is_eq(Geo.minutes(nyc(), nyc()), 0n)},
   Check{"NYC to LA is about 2450 miles", between(Geo.tenths(nyc(), la()), 24000n, 25000n)},
   Check{"Chicago to Houston is about 940 miles", between(Geo.tenths(chicago(), houston()), 9200n, 9600n)},
   Check{"a degree of latitude is about 69 miles", between(Geo.tenths(T.Point{400000n, 740000n}, T.Point{410000n, 740000n}), 680n, 700n)},
   Check{"drive time grows with distance", Nat.is_lt(Geo.minutes(nyc(), near_nyc(1000n)), Geo.minutes(nyc(), near_nyc(9000n)))}]

def solve_checks() -> List<&2, Check>:
  [Check{"the solved plan is valid", P.Plan.valid(inst(), solved())},
   Check{"the parallel checker agrees", P.Plan.check(inst(), solved())},
   Check{"every job gets a stop", Nat.is_eq(count_routes(T.Plan.routes(solved())), 4n)},
   Check{"no stop is late", Nat.is_eq(total_late(T.Plan.routes(solved())), 0n)},
   Check{"no stop is out of zip", Nat.is_eq(total_outside(T.Plan.routes(solved())), 0n)},
   Check{"a short day is respected", Nat.is_eq(overtime(T.Plan.routes(S.solve(tune(), short_inst(), 10n, 12n))), 0n)},
   Check{"what doesn't fit waits", Nat.is_gt(waiting(S.solve(tune(), short_inst(), 10n, 12n)), 0n)},
   Check{"the tightest deadline goes first", Nat.is_eq(exceptions(S.solve(tune(), tight_inst(), 10n, 11n)), 0n)},
   Check{"urgent uncovered work crosses a zip", Nat.is_eq(total_outside(T.Plan.routes(S.solve(tune(), outside_inst(), 10n, 12n))), 1n)},
   Check{"past the cap it goes to exceptions", Nat.is_eq(exceptions(S.solve(tune(), too_far_inst(), 10n, 12n)), 1n)},
   Check{"a synthetic instance places all 400 jobs", Nat.is_eq(count_routes(T.Plan.routes(bench_plan())), 400n)},
   Check{"a synthetic instance has no late stops", Nat.is_eq(total_late(T.Plan.routes(bench_plan())), 0n)},
   Check{"a synthetic instance has no overtime", Nat.is_eq(overtime(T.Plan.routes(bench_plan())), 0n)}]

def cancelled() -> H.State:
  after(start(), H.Cancel{next_id(start())})

def begun() -> H.State:
  progress(start(), H.Started{next_id(start())})

def heal_checks() -> List<&2, Check>:
  +i = next_id(start())
  [Check{"cancelling keeps the plan valid", valid(cancelled())},
   Check{"a cancelled job is gone", Bool.not(id_placed(cancelled(), i))},
   Check{"cancelling removes exactly one job", Nat.is_eq(placed(cancelled()), 3n)},
   Check{"starting a stop keeps the plan valid", valid(begun())},
   Check{"a started stop can't be cancelled", id_placed(after(begun(), H.Cancel{i}), i)},
   Check{"finishing keeps the plan valid", valid(progress(begun(), H.Finished{i}))},
   Check{"a finished stop can't be cancelled", id_placed(after(progress(begun(), H.Finished{i}), H.Cancel{i}), i)},
   Check{"a missed stop goes back to the backlog", Nat.is_eq(backlog(progress(begun(), H.Missed{i})), 1n)},
   Check{"a missed stop keeps the plan valid", valid(progress(begun(), H.Missed{i}))},
   Check{"a new request lands in the backlog", Nat.is_eq(backlog(after(start(), H.Request{far_job()})), 1n)},
   Check{"a new request keeps the plan valid", valid(after(start(), H.Request{far_job()}))},
   Check{"a repeated request changes nothing", Nat.is_eq(placed(after(after(start(), H.Request{far_job()}), H.Request{far_job()})), 5n)},
   Check{"a request from another state changes nothing", Nat.is_eq(placed(after(start(), H.Request{foreign_job()})), 4n)},
   Check{"a request from another state keeps the plan valid", valid(after(start(), H.Request{foreign_job()}))},
   Check{"a contractor from another state makes an instance invalid", Bool.not(P.Instance.ok(foreign_crew()))},
   Check{"an appraisal from another state makes an instance invalid", Bool.not(P.Instance.ok(foreign_jobs()))},
   Check{"releasing a stop moves it to the backlog", Nat.is_eq(backlog(after(start(), H.Release{i})), 1n)},
   Check{"backfill moves it onto a route", Nat.is_eq(backlog(after(after(start(), H.Release{i}), H.Backfill{i, 1n, 11n, 0n})), 0n)},
   Check{"backfill keeps the plan valid", valid(after(after(start(), H.Release{i}), H.Backfill{i, 1n, 11n, 0n}))},
   Check{"a sick contractor's open stops go to the backlog", Nat.is_gt(backlog(after(start(), H.Sick{1n, 10n})), 0n)},
   Check{"a sick contractor's plan stays valid", valid(after(start(), H.Sick{1n, 10n}))},
   Check{"a closed route takes no new work", Nat.is_gt(backlog(after(after(start(), H.Sick{1n, 10n}), H.Backfill{i, 1n, 10n, 0n})), 0n)},
   Check{"a reorder that loses a stop is refused", Nat.is_eq(placed(after(start(), H.Improve{1n, 10n, Nil{}})), 4n)},
   Check{"a refused reorder changes nothing", Nat.is_eq(on_routes(after(start(), H.Improve{1n, 10n, Nil{}})), 4n)}]

# Roads: five nodes, drive times in deciseconds. 0 and 1 and 2 are a two-way road,
# 0 to 2 is a slow one-way road, 2 to 3 is one-way, and 4 connects to nothing.
def road.word(+x: U32, t: List<&2, U32>) -> List<&2, U32>:
  U32.and(x, 255) <> U32.and(U32.shrn(x, 8n), 255) <> U32.and(U32.shrn(x, 16n), 255) <> U32.shrn(x, 24n) <> t

def road.edge(+from: U32, +to: U32, +cost: U32, +flags: U32, t: List<&2, U32>) -> List<&2, U32>:
  road.word(from, road.word(to, road.word(0, road.word(cost, road.word(flags, road.word(0, t))))))

def road.edges() -> List<&2, U32>:
  road.edge(0, 1, 10, 0, road.edge(1, 2, 20, 0, road.edge(0, 2, 100, 16, road.edge(2, 3, 5, 16, Nil{}))))

def road.placed(t: RG.Tally, +arcs: U32) -> Array<U32>:
  match t:
    case RG.Tally{g, _, _, _, _}:
      RG.Graph.head(g, 5, arcs)

def road.counted(t: RG.Tally) -> Array<U32>:
  match t:
    case RG.Tally{g, _, _, +arcs, _}:
      road.placed(RG.Place.chunk(road.edges(), RG.Sum.run(g, 5n), 5, 0), arcs)

def road.graph() -> Array<U32>:
  road.counted(RG.Count.chunk(road.edges(), [0 : U32^6n], 5, 0, 0, 0))

def road.cfg(+limit: U32) -> RL.Cfg:
  RL.Cfg{4096n, 256n, 5n, 5, 16, limit, 7n}

def road.rows(+d: Nat, +xs: List<&2, U32>, +ts: List<&2, U32>, +limit: U32) -> List<&2, RL.Row>:
  RL.Lanes.run(RL.Lanes.make(d, road.graph(), xs), ts, road.cfg(limit))

def road.cells(rows: List<&2, RL.Row>) -> List<&2, U32>:
  match rows:
    case Nil{}:
      Nil{}
    case +r <> t:
      List.append(&2, U32, RL.Row.cells(r), road.cells(t))

def road.time(+src: U32, +dst: U32, +limit: U32) -> Maybe<&2, U32>:
  List.head(&2, U32, road.cells(road.rows(0n, [src], [dst], limit)))

def road.is(+m: Maybe<&2, U32>, +x: U32) -> Bool:
  U32.is_eq(Maybe.default(&2, U32, m, 7), x)

def road.same(xs: List<&2, U32>, ys: List<&2, U32>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case +a <> s +b <> t:
      Bool.and(U32.is_eq(a, b), road.same(s, t))
    case _ _:
      False{}

def road.all() -> List<&2, U32>:
  [0, 1, 2, 3, 4]

def road.lanes(+d: Nat) -> Bool:
  road.same(road.cells(road.rows(d, road.all(), road.all(), 1000)), road.cells(road.rows(0n, road.all(), road.all(), 1000)))

def road.check(+xs: List<&2, U32>, +src: U32, +dst: U32) -> Maybe<&2, Nat>:
  RP.Walked.cost(RP.Path.check(road.graph(), 5, src, dst, xs))

def road.bad.of(t: RG.Tally) -> U32:
  match t:
    case RG.Tally{_, _, _, _, +bad}:
      bad

def road.bad() -> U32:
  road.bad.of(RG.Count.chunk(road.edge(0, 9, 10, 0, Nil{}), [0 : U32^6n], 5, 0, 0, 0))

def road.refused(c: RP.Cell) -> Bool:
  match c:
    case RP.Cell{_, _, _, _, bad}:
      bad

# A search left a wrong time behind: the lookup has to refuse it.
def road.tampered.cell(o: RS.Out) -> Bool:
  match o:
    case RS.Out{g, w, _, _}:
      road.refused(RP.Cell.read(g, Array.set(U32, w, 3, 1), 5n, 5, 1000, 0, 3, 1))

def road.tampered() -> Bool:
  road.tampered.cell(RS.Search.run(4096n, 256n, road.graph(), [0 : U32^7n], 5, 16, 1000, 0, 1))

# Snapping, with longitudes as their U32 bit patterns.
def snap.lon() -> U32:
  3294967296

def snap.bytes() -> List<&2, U32>:
  road.word(400010000, road.word(snap.lon(), road.word(400210000, road.word(snap.lon(), Nil{}))))

def snap.find(s: RN.Build, +lat: U32) -> RN.Near:
  match s:
    case RN.Build{c, b, _}:
      RN.Snap.find([1, 4, 16, 64], c, b, lat, snap.lon(), 4294967295n)

def snap.built(+lat: U32) -> RN.Near:
  snap.find(RN.Build.place(RN.Build.chunk(snap.bytes(), [0 : U32^3n], [0 : U32^19n], 0), 2n), lat)

def snap.node(n: RN.Near) -> U32:
  match n:
    case RN.Near{_, _, +node, _, _}:
      node

def snap.best(n: RN.Near) -> Nat:
  match n:
    case RN.Near{_, _, _, +best, _}:
      best

# A tie across a cell line: the point sits halfway between two nodes, and the
# higher numbered one is in the cell the scan reaches first.
def snap.tie.bytes() -> List<&2, U32>:
  road.word(400210000, road.word(snap.lon(), road.word(400190000, road.word(snap.lon(), Nil{}))))

def snap.tie() -> RN.Near:
  snap.find(RN.Build.place(RN.Build.chunk(snap.tie.bytes(), [0 : U32^3n], [0 : U32^19n], 0), 2n), 400200000)

# An 8 by 8 grid of two-way roads with scattered costs, big enough for the heap to
# matter. Bellman-Ford over the same edges is the reference.
def grid.size() -> Nat:
  8n

def grid.cost(+a: Nat, +b: Nat) -> Nat:
  Nat.add(1n, Nat.mod(Nat.add(Nat.mul(a, 7919n), Nat.mul(b, 104729n)), 97n))

def grid.right(+i: Nat) -> Bool:
  Nat.is_lt(Nat.add(Nat.mod(i, grid.size()), 1n), grid.size())

type GEdge is Data:
  GEdge{from: Nat, to: Nat, cost: Nat}

def grid.pick(c: Bool, +e: GEdge, t: List<&2, GEdge>) -> List<&2, GEdge>:
  match c:
    case True{}:
      e <> t
    case False{}:
      t

def grid.edges(k: Nat, +i: Nat, acc: List<&2, GEdge>) -> List<&2, GEdge>:
  match k:
    case 0n:
      acc
    case 1n+p:
      +r = Nat.add(i, 1n)
      +d = Nat.add(i, grid.size())
      grid.edges(p, 1n+i, grid.pick(grid.right(i), GEdge{i, r, grid.cost(i, r)}, grid.pick(Nat.is_lt(d, Nat.mul(grid.size(), grid.size())), GEdge{i, d, grid.cost(i, d)}, acc)))

def grid.all() -> List<&2, GEdge>:
  grid.edges(Nat.mul(grid.size(), grid.size()), 0n, Nil{})

def grid.bytes(es: List<&2, GEdge>, t: List<&2, U32>) -> List<&2, U32>:
  match es:
    case Nil{}:
      t
    case +e <> r:
      match e:
        case GEdge{+a, +b, +c}:
          road.edge(U32.from_nat(a), U32.from_nat(b), U32.from_nat(c), 0, grid.bytes(r, t))

def grid.placed(t: RG.Tally, +arcs: U32) -> Array<U32>:
  match t:
    case RG.Tally{g, _, _, _, _}:
      RG.Graph.head(g, 64, arcs)

def grid.counted(t: RG.Tally, +xs: List<&2, U32>) -> Array<U32>:
  match t:
    case RG.Tally{g, _, _, +arcs, _}:
      grid.placed(RG.Place.chunk(xs, RG.Sum.run(g, 64n), 64, 0), arcs)

def grid.graph() -> Array<U32>:
  +xs = grid.bytes(grid.all(), Nil{})
  grid.counted(RG.Count.chunk(xs, [0 : U32^10n], 64, 0, 0, 0), xs)

def grid.ids(k: Nat, +i: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match k:
    case 0n:
      List.reverse(&2, U32, acc)
    case 1n+p:
      grid.ids(p, (i + 1 : U32), i <> acc)

def grid.first(rows: List<&2, RL.Row>) -> RL.Row:
  match rows:
    case Nil{}:
      RL.Row{Nil{}, 0n, 1n}
    case +r <> _:
      r

def grid.row() -> RL.Row:
  grid.first(RL.Lanes.run(RL.Lanes.make(0n, grid.graph(), [0]), grid.ids(64n, 0, Nil{}), RL.Cfg{65536n, 256n, 64n, 64, 300, 1000000, 10n}))

# dist[i] after relaxing every edge both ways, round after round.
def ref.get(xs: List<&2, Nat>, +i: Nat) -> Nat:
  Maybe.default(&2, Nat, List.get(&2, Nat, xs, i), 0n)

def ref.lower(+xs: List<&2, Nat>, +i: Nat, +d: Nat) -> List<&2, Nat>:
  List.set(&2, Nat, xs, i, Nat.min(ref.get(xs, i), d))

def ref.edge(+xs: List<&2, Nat>, +e: GEdge) -> List<&2, Nat>:
  match e:
    case GEdge{+a, +b, +c}:
      +ys = ref.lower(xs, b, Nat.add(ref.get(xs, a), c))
      ref.lower(ys, a, Nat.add(ref.get(ys, b), c))

def ref.pass(es: List<&2, GEdge>, +xs: List<&2, Nat>) -> List<&2, Nat>:
  match es:
    case Nil{}:
      xs
    case +e <> t:
      ref.pass(t, ref.edge(xs, e))

def ref.run(k: Nat, +xs: List<&2, Nat>) -> List<&2, Nat>:
  match k:
    case 0n:
      xs
    case 1n+p:
      ref.run(p, ref.pass(grid.all(), xs))

def ref.start() -> List<&2, Nat>:
  0n <> List.replicate(Nat, 63n, 1000000n)

def ref.same(xs: List<&2, U32>, ys: List<&2, Nat>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case +a <> s +b <> t:
      Bool.and(Nat.is_eq(U32.to_nat(a), b), ref.same(s, t))
    case _ _:
      False{}

def road_checks() -> List<&2, Check>:
  [Check{"the quicker way round beats the slow direct road", road.is(road.time(0, 2, 1000), 30)},
   Check{"a route chains roads", road.is(road.time(0, 3, 1000), 35)},
   Check{"a one-way road drives forwards", road.is(road.time(2, 3, 1000), 5)},
   Check{"a one-way road can't be driven backwards", road.is(road.time(3, 2, 1000), RL.Unreachable())},
   Check{"a stop past the limit is out of reach", road.is(road.time(0, 2, 20), RL.Unreachable())},
   Check{"a stop exactly at the limit is in reach", road.is(road.time(0, 2, 30), 30)},
   Check{"a road nothing joins is out of reach", road.is(road.time(0, 4, 1000), RL.Unreachable())},
   Check{"a stop to itself takes no time", road.is(road.time(1, 1, 1000), 0)},
   Check{"two lanes give the same matrix as one", road.lanes(1n)},
   Check{"four lanes give the same matrix as one", road.lanes(2n)},
   Check{"a real arc passes the walk", Maybe.is_some(&2, Nat, road.check([0], 0, 1))},
   Check{"an arc from another node fails the walk", Maybe.is_none(&2, Nat, road.check([2], 0, 1))},
   Check{"a path ending in the wrong place fails the walk", Maybe.is_none(&2, Nat, road.check([0], 0, 2))},
   Check{"an edge past the last node is counted as bad", U32.is_eq(road.bad(), 1)},
   Check{"a time the walk doesn't confirm is refused", road.tampered()},
   Check{"snapping finds a closer node in the next cell", U32.is_eq(snap.node(snap.built(400195000)), 1)},
   Check{"snapping widens until it finds a road", U32.is_eq(snap.node(snap.built(402010000)), 1)},
   Check{"a point with no road nearby snaps to nothing", Nat.is_eq(snap.best(snap.built(600000000)), RN.Far())},
   Check{"a tie goes to the lower numbered node", U32.is_eq(snap.node(snap.tie()), 0)},
   Check{"a search settles each node once", Nat.is_eq(RL.Row.settled(grid.row()), 64n)},
   Check{"a search finds the shortest time to every node", ref.same(RL.Row.cells(grid.row()), ref.run(63n, ref.start()))}]

def show(c: Check) -> String:
  match c:
    case Check{n, True{}}:
      "ok    " ++ n
    case Check{n, False{}}:
      "FAIL  " ++ n

def failed(xs: List<&2, Check>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Check{n, True{}} <> t:
      failed(t)
    case Check{n, False{}} <> t:
      1n+failed(t)

def print_all(xs: List<&2, Check>) -> IO(Unit):
  match xs:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case h <> t:
      IO.bind(Unit, Unit, IO.print(show(h)), u => print_all(t))

def finish(n: Nat) -> IO(Unit):
  match n:
    case 0n:
      IO.print("all scenarios pass")
    case 1n+p:
      IO.die(Unit, 1, Nat.show(n) ++ " scenarios failed")

def main() -> IO(Unit):
  +all = List.append(&2, Check, geo_checks(), List.append(&2, Check, solve_checks(), List.append(&2, Check, heal_checks(), road_checks())))
  IO.bind(Unit, Unit, print_all(all), u => finish(failed(all)))
