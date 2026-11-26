import Base
import ../core/types.bend as T
import ../core/lifecycle.bend as Life
import ../core/jobs.bend as J
import ../core/route.bend as R
import ../core/plan.bend as P
import ../core/heal.bend as H
import ../core/solve.bend as S
import ../core/geo.bend as Geo
import ../core/times.bend as Tm
import ../core/nation.bend as N
import ../solver/synth.bend as Syn
import ../solver/load.bend as Ld
import ../solver/baseline.bend as B
import ../solver/report.bend as Rp
import ../road/graph.bend as RG
import ../road/search.bend as RS
import ../road/path.bend as RP
import ../road/snap.bend as RN
import ../road/lanes.bend as RL
import ../web/json.bend as WJ
import ../web/schema.bend as WS
import ../web/api.bend as WA
import ../web/openapi.bend as WO
import ../web/store.bend as St
import ../web/utf8.bend as U

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
    [job(1n, 100n, 100n, 10n), job(2n, 200n, 100n, 10n), job(3n, 300n, 101n, 11n), job(4n, 400n, 102n, 10n)], 60n, ny(), Tm.none()}

# Georgia's FIPS code, for anything that belongs to another state's instance.
def foreign_job() -> T.Appraisal:
  T.Appraisal{9n, near_nyc(100n), 100n, 10n, 20n, 13n}

def foreign_crew() -> T.Instance:
  T.Instance{[T.Contractor{1n, nyc(), [100n], 480n, [10n], 13n}], [job(1n, 100n, 100n, 10n)], 60n, ny(), Tm.none()}

def foreign_jobs() -> T.Instance:
  T.Instance{[crew(1n, [100n], 480n)], [foreign_job()], 60n, ny(), Tm.none()}

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
    job(5n, 500n, 100n, 20n), job(6n, 600n, 100n, 20n), job(7n, 700n, 100n, 20n), job(8n, 800n, 100n, 20n)], 60n, ny(), Tm.none()}

# One day with room for about two stops, and the job due first listed last.
def tight_inst() -> T.Instance:
  T.Instance{[crew(1n, [100n], 60n)], [job(1n, 100n, 100n, 30n), job(2n, 200n, 100n, 30n), job(3n, 300n, 100n, 30n), job(4n, 400n, 100n, 10n)], 60n, ny(), Tm.none()}

# Work nobody covers, due inside the horizon: it should cross a zip and be flagged.
def outside_inst() -> T.Instance:
  T.Instance{[crew(1n, [100n], 480n)], [job(1n, 100n, 555n, 10n)], 60n, ny(), Tm.none()}

# Same, but too far for the cap.
def too_far_inst() -> T.Instance:
  T.Instance{[crew(1n, [100n], 2000n)], [T.Appraisal{1n, la(), 555n, 10n, 20n, ny()}], 60n, ny(), Tm.none()}

# One job a short way off, with a road table that says the drive takes each way
# minutes. Due past the horizon, so if it can't fit it waits.
def road_inst(+each: Nat) -> T.Instance:
  T.Instance{[crew(1n, [100n], 480n)], [job(1n, 100n, 100n, 20n)], 60n, ny(),
    Tm.of(61n, [Tm.Entry{nyc(), near_nyc(100n), each}, Tm.Entry{near_nyc(100n), nyc(), each}])}

def road_plan(+each: Nat) -> T.Plan:
  S.solve(tune(), road_inst(each), 10n, 12n)

def worked(routes: List<&2, T.Route>) -> Nat:
  match routes:
    case Nil{}:
      0n
    case +r <> t:
      Nat.add(T.Audit.minutes(T.Route.audit(r)), worked(t))

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

# A turn graph straight from turns.bin records: 0 to 1 to 2 beats 0 to 2 direct.
def turns.record(+from: U32, +to: U32, +cost: U32, t: List<&2, U32>) -> List<&2, U32>:
  road.word(from, road.word(to, road.word(cost, t)))

def turns.bytes() -> List<&2, U32>:
  turns.record(0, 1, 5, turns.record(1, 2, 7, turns.record(0, 2, 20, turns.record(2, 3, 1, Nil{}))))

def turns.placed(t: RG.Tally) -> Array<U32>:
  match t:
    case RG.Tally{g, _, _, +arcs, _}:
      RG.Graph.head(g, 4, arcs)

def turns.counted(t: RG.Tally) -> Array<U32>:
  match t:
    case RG.Tally{g, _, _, _, _}:
      turns.placed(RG.Turn.placed(turns.bytes(), RG.Sum.run(g, 4n), 4, 0))

def turns.graph() -> Array<U32>:
  turns.counted(RG.Turn.counted(turns.bytes(), [0 : U32^5n], 4, 0, 0))

def turns.time() -> List<&2, U32>:
  road.cells(RL.Lanes.run(RL.Lanes.make(0n, turns.graph(), [0]), [3], RL.Cfg{4096n, 256n, 4n, 4, 16, 1000, 7n}))

def turns.bad.of(t: RG.Tally) -> U32:
  match t:
    case RG.Tally{_, _, _, _, +bad}:
      bad

def turns.bad() -> U32:
  turns.bad.of(RG.Turn.counted(turns.record(0, 9, 5, Nil{}), [0 : U32^5n], 4, 0, 0))

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
   Check{"a search finds the shortest time to every node", ref.same(RL.Row.cells(grid.row()), ref.run(63n, ref.start()))},
   Check{"a turn graph loads from its records", road.same(turns.time(), [13])},
   Check{"a turn to a node past the last is counted as bad", U32.is_eq(turns.bad(), 1)}]

# Road times
# ----------

def times.table() -> T.Times:
  Tm.of(61n, [Tm.Entry{nyc(), near_nyc(1000n), 37n}, Tm.Entry{near_nyc(1000n), near_nyc(2000n), 9n}, Tm.Entry{nyc(), near_nyc(2000n), 5n}])

def times.get(+a: T.Point, +b: T.Point) -> Nat:
  Tm.minutes(times.table(), a, b)

# Row i of a bigger table: from near_nyc(7i) to near_nyc(7j) takes i + j minutes.
def times.many.row(n: Nat, +i: Nat, acc: List<&2, Tm.Entry>) -> List<&2, Tm.Entry>:
  match n:
    case 0n:
      acc
    case 1n+p:
      +j = p
      times.many.row(j, i, Tm.Entry{near_nyc(Nat.mul(i, 7n)), near_nyc(Nat.mul(j, 7n)), Nat.add(i, j)} <> acc)

def times.many.rows(n: Nat, +size: Nat, acc: List<&2, Tm.Entry>) -> List<&2, Tm.Entry>:
  match n:
    case 0n:
      acc
    case 1n+p:
      +i = p
      times.many.rows(i, size, times.many.row(size, i, acc))

def times.many() -> T.Times:
  Tm.of(0n, times.many.rows(40n, 40n, Nil{}))

def times.sum.row(n: Nat, +t: T.Times, +i: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      +j = p
      Nat.add(Tm.minutes(t, near_nyc(Nat.mul(i, 7n)), near_nyc(Nat.mul(j, 7n))), times.sum.row(j, t, i))

def times.sum(n: Nat, +t: T.Times, +size: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      +i = p
      Nat.add(times.sum.row(size, t, i), times.sum(i, t, size))

def times_checks() -> List<&2, Check>:
  [Check{"a pair in the table takes the table's time", Nat.is_eq(times.get(nyc(), near_nyc(1000n)), 37n)},
   Check{"every pair in a row is found", Nat.is_eq(times.get(nyc(), near_nyc(2000n)), 5n)},
   Check{"a table time can beat the straight line", Nat.is_lt(times.get(nyc(), near_nyc(2000n)), Geo.minutes(nyc(), near_nyc(2000n)))},
   Check{"the table is one-way", Nat.is_eq(times.get(near_nyc(1000n), nyc()), 61n)},
   Check{"a missing pair is never under the table's limit", Nat.is_eq(times.get(near_nyc(2000n), near_nyc(1000n)), 61n)},
   Check{"a far missing pair takes the straight line", Nat.is_eq(times.get(nyc(), la()), Geo.minutes(nyc(), la()))},
   Check{"the same point is zero minutes", Nat.is_eq(times.get(nyc(), nyc()), 0n)},
   Check{"no table means straight-line times", Nat.is_eq(Tm.minutes(Tm.none(), nyc(), near_nyc(9000n)), Geo.minutes(nyc(), near_nyc(9000n)))},
   Check{"a route's minutes come from the road times", Nat.is_eq(worked(T.Plan.routes(road_plan(200n))), 420n)},
   Check{"a plan on road times is valid", P.Plan.valid(road_inst(200n), road_plan(200n))},
   Check{"work too far by road waits", Nat.is_eq(count_routes(T.Plan.routes(road_plan(250n))), 0n)},
   Check{"a 1,600-pair table finds every pair", Nat.is_eq(times.sum(40n, times.many(), 40n), 60840n)}]

# The national solve
# ------------------

def Nats.same(xs: List<&2, Nat>, ys: List<&2, Nat>) -> Bool:
  T.Nats.is_eq(xs, ys)

def nation() -> List<&2, T.Instance>:
  [inst(), short_inst(), tight_inst(), outside_inst(), road_inst(200n), bench()]

def nation.scores(ps: List<&2, T.Plan>) -> List<&2, Nat>:
  match ps:
    case Nil{}:
      Nil{}
    case +p <> t:
      S.score(p) <> nation.scores(t)

def nation.valid(xs: List<&2, T.Instance>, ps: List<&2, T.Plan>) -> Bool:
  match xs ps:
    case +x <> xt +p <> pt:
      Bool.and(P.Plan.valid(x, p), nation.valid(xt, pt))
    case Nil{} Nil{}:
      True{}
    case _ _:
      False{}

def nation.plans(+fuel: Nat) -> List<&2, T.Plan>:
  N.national(fuel, tune(), nation(), 20000n, 20005n)

def nation.one(+i: T.Instance) -> T.Plan:
  S.solve(tune(), i, 20000n, 20005n)

def nation_checks() -> List<&2, Check>:
  [Check{"a national solve gives one plan per state", Nat.is_eq(List.length(&2, T.Plan, nation.plans(3n)), 6n)},
   Check{"every state's plan is valid for its instance", nation.valid(nation(), nation.plans(3n))},
   Check{"forking the states gives the same plans", Nats.same(nation.scores(nation.plans(3n)), nation.scores(nation.plans(0n)))},
   Check{"a state's plan is its own solve", Nats.same(nation.scores(nation.plans(2n)), nation.scores([nation.one(inst()), nation.one(short_inst()), nation.one(tight_inst()), nation.one(outside_inst()), nation.one(road_inst(200n)), nation.one(bench())]))},
   Check{"work counts jobs times routes", Nat.is_eq(N.State.work(bench()), Nat.add(1n, Nat.mul(400n, 40n)))},
   Check{"the split leaves the biggest state alone", Nat.is_eq(N.States.split_at(nation(), Nat.div(N.States.work(nation()), 2n), 0n), 5n)}]

# Baselines and reports
# ---------------------

# Two crews at the same home, both covering zip 100. First fit loads crew 1's
# first day before anything else; the planner spreads the work.
def base.inst() -> T.Instance:
  T.Instance{[crew(1n, [100n], 480n), crew(2n, [100n], 480n)],
    [job(1n, 100n, 100n, 11n), job(2n, 200n, 100n, 11n), job(3n, 300n, 100n, 11n), job(4n, 400n, 100n, 11n)], 60n, ny(), Tm.none()}

def base.first() -> T.Plan:
  B.first_fit(base.inst(), 10n, 12n)

def base.near() -> T.Plan:
  B.nearest(base.inst(), 10n, 12n)

# Crew 1 lives far from the work, crew 2 next to it.
def near.inst() -> T.Instance:
  T.Instance{[T.Contractor{1n, near_nyc(9000n), [100n], 480n, [10n], ny()}, crew(2n, [100n], 480n)], [job(1n, 100n, 100n, 10n)], 60n, ny(), Tm.none()}

def route.on(routes: List<&2, T.Route>, +c: Nat, +d: Nat) -> Nat:
  match routes:
    case Nil{}:
      0n
    case +r <> t:
      Nat.add(Bool.pick(Nat, H.Route.at(r, c, d), List.length(&2, T.Stop, T.Route.stops(r)), 0n), route.on(t, c, d))

def stats(+inst: T.Instance, +plan: T.Plan) -> Rp.Stats:
  Rp.of(inst, plan, 10n, 12n)

def base_checks() -> List<&2, Check>:
  [Check{"the first-fit baseline is valid", P.Plan.valid(base.inst(), base.first())},
   Check{"the first-fit baseline places every job", Nat.is_eq(count_routes(T.Plan.routes(base.first())), 4n)},
   Check{"first fit fills the first route before the next", Nat.is_eq(route.on(T.Plan.routes(base.first()), 1n, 10n), 4n)},
   Check{"the nearest baseline is valid", P.Plan.valid(near.inst(), B.nearest(near.inst(), 10n, 11n))},
   Check{"the nearest baseline picks the nearest contractor", Nat.is_eq(route.on(T.Plan.routes(B.nearest(near.inst(), 10n, 11n)), 2n, 10n), 1n)},
   Check{"a baseline never leaves its zips", Nat.is_eq(total_outside(T.Plan.routes(B.first_fit(outside_inst(), 10n, 12n))), 0n)},
   Check{"so urgent work it can't reach is an exception", Nat.is_eq(exceptions(B.first_fit(outside_inst(), 10n, 12n)), 1n)},
   Check{"a report counts placed jobs", Nat.is_eq(Rp.Stats.placed(stats(base.inst(), base.first())), 4n)},
   Check{"a report adds up drive time", Nat.is_eq(Rp.Stats.drive(stats(road_inst(200n), road_plan(200n))), 400n)},
   Check{"a report finds the longest day", Nat.is_eq(Rp.Stats.peak(stats(road_inst(200n), road_plan(200n))), 420n)},
   Check{"a missed job that couldn't fit isn't counted as feasible", Nat.is_eq(Rp.Stats.feasible(stats(too_far_inst(), S.solve(tune(), too_far_inst(), 10n, 12n))), 0n)},
   Check{"a missed job that could have fit is counted", Nat.is_eq(Rp.Stats.feasible(stats(outside_inst(), B.first_fit(outside_inst(), 10n, 12n))), 1n)},
   Check{"a report counts every contractor with routes", Nat.is_eq(Rp.Stats.crews(stats(base.inst(), base.first())), 2n)},
   Check{"a report finds the busiest contractor's week", Nat.is_eq(Rp.Stats.wpeak(stats(road_inst(200n), road_plan(200n))), 420n)},
   Check{"a job no empty route can take counts as impossible", Nat.is_eq(Rp.Stats.impossible(stats(too_far_inst(), S.solve(tune(), too_far_inst(), 10n, 12n))), 1n)},
   Check{"a job an empty route could take isn't impossible", Nat.is_eq(Rp.Stats.impossible(stats(outside_inst(), B.first_fit(outside_inst(), 10n, 12n))), 0n)},
   Check{"work that can wait isn't counted as missed", Nat.is_eq(Rp.Stats.feasible(stats(short_inst(), T.Plan{S.blank(Tm.none(), T.Instance.crews(short_inst()), 10n, 12n), T.Instance.jobs(short_inst()), Nil{}})), 0n)},
   Check{"the planner misses nothing that fits", Nat.is_eq(Rp.Stats.feasible(stats(bench(), bench_plan())), 0n)}]

# Loading files
# -------------

# Delaware, two contractors and one job, in instance.bin words: crew 1 works days
# 20000 and 20002, crew 4 day 20006 and covers no zips.
def load.words() -> List<&2, Nat>:
  [1n, 10n, 60n, 20000n, 7n, 2n, 1n,
   1n, 390000n, 755000n, 480n, 5n, 2n, 5n, 9n,
   4n, 391000n, 756000n, 360n, 64n, 0n,
   3n, 392000n, 757000n, 9n, 20003n, 20n]

def load.file() -> Ld.Got:
  Ld.instance(load.words())

def load.inst() -> T.Instance:
  Ld.Got.inst(load.file())

def load.crew(+n: Nat) -> T.Contractor:
  Maybe.default(&2, T.Contractor, List.get(&2, T.Contractor, T.Instance.crews(load.inst()), n), T.Contractor{0n, nyc(), Nil{}, 0n, Nil{}, 0n})

def load.job() -> T.Appraisal:
  Maybe.default(&2, T.Appraisal, List.get(&2, T.Appraisal, T.Instance.jobs(load.inst()), 0n), job(0n, 0n, 0n, 0n))

# Their matrix, in row order over homes then sites, as the bytes of matrix.bin.
def load.byte(+x: Nat, t: List<&2, U32>) -> List<&2, U32>:
  +w = U32.from_nat(x)
  U32.and(w, 255) <> U32.and(U32.shrn(w, 8n), 255) <> U32.and(U32.shrn(w, 16n), 255) <> U32.shrn(w, 24n) <> t

def load.bytes(xs: List<&2, Nat>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> t:
      load.byte(x, load.bytes(t))

def load.cells() -> List<&2, Nat>:
  [3n, 0n, 6000n, 601n, 6000n, 0n, 4294967295n, 1800n, 4294967295n, 0n]

def load.mx() -> Ld.Mx:
  Ld.Mx.bytes(load.bytes(load.cells()), Ld.Mx.start(Ld.keys(load.inst())))

def load.times() -> T.Times:
  Ld.Mx.times(load.mx(), 36000n)

def load.home(+n: Nat) -> T.Point:
  T.Contractor.home(load.crew(n))

def load_checks() -> List<&2, Check>:
  [Check{"an instance file gives its state, cap and horizon", Bool.and(Nat.is_eq(T.Instance.state(load.inst()), 10n), Bool.and(Nat.is_eq(T.Instance.cap(load.inst()), 60n), Bool.and(Nat.is_eq(Ld.Got.first(load.file()), 20000n), Nat.is_eq(Ld.Got.days(load.file()), 7n))))},
   Check{"an instance file gives every crew and job", Bool.and(Nat.is_eq(List.length(&2, T.Contractor, T.Instance.crews(load.inst())), 2n), Nat.is_eq(List.length(&2, T.Appraisal, T.Instance.jobs(load.inst())), 1n))},
   Check{"a crew record reads in full", T.Contractor.is_eq(load.crew(0n), T.Contractor{1n, T.Point{390000n, 755000n}, [5n, 9n], 480n, [20000n, 20002n], 10n})},
   Check{"a crew with no zips reads too", T.Contractor.is_eq(load.crew(1n), T.Contractor{4n, T.Point{391000n, 756000n}, Nil{}, 360n, [20006n], 10n})},
   Check{"a job record reads in full", T.Appraisal.is_eq(load.job(), T.Appraisal{3n, T.Point{392000n, 757000n}, 9n, 20003n, 20n, 10n})},
   Check{"a loaded instance is a valid instance", P.Instance.ok(load.inst())},
   Check{"a bad version reads as an empty instance", Nat.is_eq(List.length(&2, T.Contractor, T.Instance.crews(Ld.Got.inst(Ld.instance([2n, 10n])))), 0n)},
   Check{"a matrix file holds a time per pair", Ld.Mx.ok(load.mx(), 3n)},
   Check{"a matrix missing its last word is refused", Bool.not(Ld.Mx.ok(Ld.Mx.bytes(load.bytes([3n, 0n, 6000n, 601n, 6000n, 0n, 4294967295n, 1800n, 4294967295n]), Ld.Mx.start(Ld.keys(load.inst()))), 3n))},
   Check{"a matrix with the wrong count is refused", Bool.not(Ld.Mx.ok(load.mx(), 4n))},
   Check{"deciseconds round up to minutes", Bool.and(Nat.is_eq(Tm.minutes(load.times(), load.home(0n), load.home(1n)), 10n), Nat.is_eq(Tm.minutes(load.times(), load.home(0n), T.Appraisal.site(load.job())), 2n))},
   Check{"a time is read in its own direction", Nat.is_eq(Tm.minutes(load.times(), T.Appraisal.site(load.job()), load.home(0n)), 3n)},
   Check{"an unreachable pair is at least the limit", Nat.is_ge(Tm.minutes(load.times(), load.home(1n), T.Appraisal.site(load.job())), 61n)}]

# The web layer
# -------------

def web.head(status: String, length: String, extra: String) -> String:
  "HTTP/1.1 " ++ status ++ "\r\nConnection: close\r\nContent-Type: application/json\r\nContent-Length: " ++ length ++ "\r\n" ++ extra ++ "\r\n"

def web.is(request: String, response: String) -> Bool:
  WJ.Text.same(WA.Handled.response(WA.Api.handle(request, St.Store.empty())), response)

# A JSON text reads and prints back unchanged.
def web.echo.got(m: Maybe<&2, WJ.Json>, s: String) -> Bool:
  match m:
    case Some{j}:
      WJ.Text.same(WJ.Json.print(j), s)
    case None{}:
      False{}

def web.echo(+s: String) -> Bool:
  web.echo.got(WJ.Json.parse(s), s)

def web.refused(s: String) -> Bool:
  Bool.not(Maybe.is_some(&2, WJ.Json, WJ.Json.parse(s)))

def web.err() -> WS.Schema:
  WA.Schemas.error()

def web.reads.got(m: Maybe<&2, WJ.Json>) -> Bool:
  match m:
    case Some{j}:
      Maybe.is_some(&2, WS.Value(web.err()), WS.decode(web.err(), j))
    case None{}:
      False{}

def web.reads(s: String) -> Bool:
  web.reads.got(WJ.Json.parse(s))

# Two definitions of one component name, one with an extra field.
def web.clash() -> List<&2, WS.Schema>:
  [WS.SObj{"A", WS.SField{"x", WS.SStr{}, WS.SEnd{}}},
   WS.SObj{"A", WS.SField{"x", WS.SStr{}, WS.SField{"y", WS.SStr{}, WS.SEnd{}}}}]

def web.twice() -> WS.Schema:
  WS.SObj{"A", WS.SField{"x", WS.SStr{}, WS.SOpt{"x", WS.SNat{}, WS.SEnd{}}}}

def web.nat(n: Nat) -> Bool:
  Maybe.is_some(&2, Nat, WS.decode(WS.SNat{}, WJ.JNum{n}))

# Appraisal requests, run against a store the way the web process runs them:
# each change a response brings is applied before the next request.

def web.post(path: String, +body: String) -> String:
  "POST " ++ path ++ " HTTP/1.1\r\nContent-Type: application/json\r\nContent-Length: " ++ Nat.show(WJ.Text.bytes(body, 0n)) ++ "\r\n\r\n" ++ body

def web.get(path: String) -> String:
  "GET " ++ path ++ " HTTP/1.1\r\n\r\n"

def web.draft(key: String, zip: String, state: String) -> String:
  "{\"key\":\"" ++ key ++ "\",\"address\":\"1 Main St\",\"zip\":\"" ++ zip ++ "\",\"state\":\"" ++ state ++ "\",\"due\":\"2026-12-01\"}"

def web.create(key: String) -> String:
  web.post("/api/v1/appraisals", web.draft(key, "78701", "TX"))

def web.rec(id: String, key: String, status: String) -> String:
  "{\"id\":\"" ++ id ++ "\",\"key\":\"" ++ key ++ "\",\"address\":\"1 Main St\",\"zip\":\"78701\",\"state\":\"TX\",\"due\":\"2026-12-01\",\"status\":\"" ++ status ++ "\"}"

def web.after(m: Maybe<&2, St.Change>, +s: St.Store) -> St.Store:
  match m:
    case None{}:
      s
    case Some{c}:
      St.Store.apply(s, c)

def web.step(+s: St.Store, +request: String) -> St.Store:
  web.after(WA.Handled.change(WA.Api.handle(request, s)), s)

def web.run(rs: List<&2, String>, +s: St.Store) -> St.Store:
  match rs:
    case Nil{}:
      s
    case Con{r, rest}:
      web.run(rest, web.step(s, r))

# The store after the requests rs, from an empty one.
def web.store(rs: List<&2, String>) -> St.Store:
  web.run(rs, St.Store.empty())

def web.answers(+s: St.Store, request: String, status: String, +body: String) -> Bool:
  WJ.Text.same(WA.Handled.response(WA.Api.handle(request, s)), web.head(status, Nat.show(WJ.Text.bytes(body, 0n)), "") ++ body)

def web.writes(+s: St.Store, request: String) -> Bool:
  Maybe.is_some(&2, St.Change, WA.Handled.change(WA.Api.handle(request, s)))

def web.ascii(s: String) -> List<&2, U32>:
  match s:
    case SNil{}:
      []
    case SCon{c, t}:
      U32.from_nat(WJ.Text.code(c)) <> web.ascii(t)

def web.found(+s: St.Store, id: String) -> Bool:
  Maybe.is_some(&2, St.Rec, St.Store.find(id, St.Store.recs(s)))

def web.snap(m: Maybe<&2, St.Snap>) -> Bool:
  match m:
    case Some{St.Snap{n, +s}}:
      Nat.is_eq(n, 7n) && Nat.is_eq(St.Store.count(s), 2n) && web.found(s, "a1") && web.found(s, "a2")
    case None{}:
      False{}

def web.two() -> St.Store:
  web.store([web.create("k1"), web.create("k2")])

def web.cancel(id: String) -> String:
  web.post("/api/v1/appraisals/" ++ id ++ "/cancel", "")

# Two appraisals, the first cancelled.
def web.one_cancelled() -> St.Store:
  web.run([web.cancel("a1")], web.two())

# A log with a good line, a line that isn't a change, a cancel, and a last
# line cut off by a crash.
def web.log() -> String:
  "{\"requested\":{\"id\":\"a1\",\"key\":\"k1\",\"address\":\"1 Main St\",\"zip\":\"78701\",\"state\":\"TX\",\"due\":\"2026-12-01\",\"status\":\"open\"}}\nnot a change\n{\"cancelled\":\"a1\"}\n{\"requested\":{\"id\":\"a2\""

def web.replay() -> St.Replay:
  St.Replay.feed(web.ascii(web.log()), St.Replay.start(0n, St.Store.empty()))

def web.cancelled_in(+s: St.Store) -> Bool:
  web.answers(s, web.get("/api/v1/appraisals/a1"), "200 OK", web.rec("a1", "k1", "cancelled"))

def web.replayed(+r: St.Replay) -> Bool:
  Nat.is_eq(St.Replay.lines(r), 4n) && Nat.is_eq(St.Replay.bad(r), 2n) && web.cancelled_in(St.Replay.store(r)) && Bool.not(web.found(St.Replay.store(r), "a2"))

def web.skipped(+r: St.Replay) -> Bool:
  Nat.is_eq(St.Replay.lines(r), 3n) && Bool.not(web.found(St.Replay.store(r), "a1"))

def web.not_found() -> String:
  "{\"error\":\"not_found\",\"detail\":\"No appraisal has this id\"}"

# "P /" with Content-Length: 2, then the given body bytes.
def web.sized(body: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, web.ascii("P / HTTP/1.1\r\nContent-Length: 2\r\n\r\n"), body)

def web_checks() -> List<&2, Check>:
  [Check{"GET /api/health answers 200 with its body", web.is("GET /api/health HTTP/1.1\r\nHost: localhost\r\n\r\n", web.head("200 OK", "15", "") ++ "{\"status\":\"ok\"}")},
   Check{"a query string doesn't change the route", web.is("GET /api/health?verbose=1 HTTP/1.1\r\n\r\n", web.head("200 OK", "15", "") ++ "{\"status\":\"ok\"}")},
   Check{"the wrong method on a known path is 405 with Allow", web.is("POST /api/health HTTP/1.1\r\n\r\n", web.head("405 Method Not Allowed", "30", "Allow: GET, HEAD\r\n") ++ "{\"error\":\"method_not_allowed\"}")},
   Check{"an unknown path is 404", web.is("GET /api/nope HTTP/1.1\r\n\r\n", web.head("404 Not Found", "21", "") ++ "{\"error\":\"not_found\"}")},
   Check{"a request with no request line is 400", web.is("hello", web.head("400 Bad Request", "23", "") ++ "{\"error\":\"bad_request\"}")},
   Check{"JSON prints back the way it was read", Bool.and(web.echo("{\"a\":[1,true,null,\"x\\n\"],\"b\":{}}"), web.echo("[]"))},
   Check{"JSON numbers are whole, unsigned and at most 14 digits", Bool.and(web.refused("01"), Bool.and(web.refused("1.5"), Bool.and(web.refused("-1"), Bool.and(web.refused("123456789012345"), web.echo("12345678901234")))))},
   Check{"broken JSON is refused", Bool.and(web.refused("[1,]"), Bool.and(web.refused("{\"a\" 1}"), Bool.and(web.refused("tru"), web.refused("\"\\ud83d\""))))},
   Check{"an object decodes with or without its optional field", Bool.and(web.reads("{\"error\":\"x\"}"), web.reads("{\"detail\":\"y\",\"error\":\"x\"}"))},
   Check{"an object with a missing, unknown or repeated field is refused", Bool.not(Bool.or(web.reads("{\"detail\":\"y\"}"), Bool.or(web.reads("{\"error\":\"x\",\"extra\":1}"), web.reads("{\"error\":\"x\",\"error\":\"y\"}"))))},
   Check{"Content-Length counts UTF-8 bytes", Nat.is_eq(WJ.Text.bytes("a\u{e9}\u{1f600}", 0n), 7n)},
   Check{"Json.small holds up to 14 digits and no further", Bool.and(WJ.Json.small(WJ.Json.Max()), Bool.not(WJ.Json.small(Nat.add(WJ.Json.Max(), 1n))))},
   Check{"the decoder refuses a number the parser would refuse", Bool.and(web.nat(WJ.Json.Max()), Bool.not(web.nat(Nat.add(WJ.Json.Max(), 1n))))},
   Check{"the request line ends at its first space and the path at its first ?", web.is("GET /api/health?a=1?b HTTP/1.1\r\nX-Note: a b c ? d\r\n\r\n", web.head("200 OK", "15", "") ++ "{\"status\":\"ok\"}")},
   Check{"a request with a 200,000 byte header still parses", web.is("GET /api/health HTTP/1.1\r\nX-Pad: " ++ String.repeat("a", 200000n) ++ "\r\n\r\n", web.head("200 OK", "15", "") ++ "{\"status\":\"ok\"}")},
   Check{"HEAD gets a GET route's headers with no body", web.is("HEAD /api/health HTTP/1.1\r\n\r\n", web.head("200 OK", "15", ""))},
   Check{"HEAD on an unknown path is 404 with no body", web.is("HEAD /api/nope HTTP/1.1\r\n\r\n", web.head("404 Not Found", "21", ""))},
   Check{"empty lines before the request line are ignored", web.is("\r\n\r\nGET /api/health HTTP/1.1\r\n\r\n", web.head("200 OK", "15", "") ++ "{\"status\":\"ok\"}")},
   Check{"the spec refuses two definitions of one name", Bool.and(Bool.not(WO.Spec.agree(web.clash())), WO.Spec.agree([WA.Schemas.error(), WA.Schemas.error()]))},
   Check{"a schema naming a field twice is not distinct", Bool.and(Bool.not(WS.Schema.distinct(web.twice())), Bool.not(WA.Answers.distinct([WA.Answer{WA.OK{}, "", web.twice()}])))},
   Check{"items or a row in a field's place is not well formed", Bool.and(Bool.not(WS.Schema.wellformed(WS.Schema.obj("A", WS.SField{"x", WS.SItems{WS.SStr{}}, WS.SEnd{}}))), Bool.and(Bool.not(WS.Schema.wellformed(WS.SList{WS.SStr{}})), WS.Schema.wellformed(WS.Schema.list(WA.Schemas.error()))))},
   Check{"a new appraisal answers 201 with id a1, open", web.answers(St.Store.empty(), web.create("k1"), "201 Created", web.rec("a1", "k1", "open"))},
   Check{"a new appraisal is written to the log", web.writes(St.Store.empty(), web.create("k1"))},
   Check{"the second appraisal gets id a2", web.answers(web.store([web.create("k1")]), web.create("k2"), "201 Created", web.rec("a2", "k2", "open"))},
   Check{"a repeated key answers 200 with the stored appraisal", web.answers(web.store([web.create("k1")]), web.create("k1"), "200 OK", web.rec("a1", "k1", "open"))},
   Check{"a repeated key writes nothing", Bool.not(web.writes(web.store([web.create("k1")]), web.create("k1")))},
   Check{"a bad zip answers 422 with its code", web.answers(St.Store.empty(), web.post("/api/v1/appraisals", web.draft("k1", "7870", "TX")), "422 Unprocessable Content", "{\"error\":\"invalid_zip\",\"detail\":\"zip must be 5 digits\"}")},
   Check{"a bad zip writes nothing", Bool.not(web.writes(St.Store.empty(), web.post("/api/v1/appraisals", web.draft("k1", "7870", "TX"))))},
   Check{"a month past 12 answers 422", web.answers(St.Store.empty(), web.post("/api/v1/appraisals", "{\"key\":\"k\",\"address\":\"a\",\"zip\":\"78701\",\"state\":\"TX\",\"due\":\"2026-13-01\"}"), "422 Unprocessable Content", "{\"error\":\"invalid_due\",\"detail\":\"due must be a date, YYYY-MM-DD\"}")},
   Check{"an empty key answers 422", web.answers(St.Store.empty(), web.post("/api/v1/appraisals", web.draft("", "78701", "TX")), "422 Unprocessable Content", "{\"error\":\"invalid_key\",\"detail\":\"key must be 1 to 64 characters\"}")},
   Check{"a state outside the lower 48 isn't a NewAppraisal, so 400", web.answers(St.Store.empty(), web.post("/api/v1/appraisals", web.draft("k1", "78701", "HI")), "400 Bad Request", "{\"error\":\"invalid_body\"}")},
   Check{"a body that isn't JSON is 400", web.answers(St.Store.empty(), web.post("/api/v1/appraisals", "{"), "400 Bad Request", "{\"error\":\"invalid_body\"}")},
   Check{"an appraisal reads back by its id", web.answers(web.two(), web.get("/api/v1/appraisals/a2"), "200 OK", web.rec("a2", "k2", "open"))},
   Check{"an unknown id is 404", web.answers(web.two(), web.get("/api/v1/appraisals/a9"), "404 Not Found", web.not_found())},
   Check{"cancelling answers 200 with the appraisal cancelled", web.answers(web.two(), web.cancel("a1"), "200 OK", web.rec("a1", "k1", "cancelled"))},
   Check{"a cancel is kept in the store", web.cancelled_in(web.one_cancelled())},
   Check{"cancelling twice answers 200", web.answers(web.one_cancelled(), web.cancel("a1"), "200 OK", web.rec("a1", "k1", "cancelled"))},
   Check{"cancelling twice writes nothing the second time", Bool.not(web.writes(web.one_cancelled(), web.cancel("a1")))},
   Check{"cancelling an unknown id is 404", web.answers(web.two(), web.cancel("a9"), "404 Not Found", web.not_found())},
   Check{"ids aren't reused after a cancel", web.answers(web.one_cancelled(), web.create("k3"), "201 Created", web.rec("a3", "k3", "open"))},
   Check{"the wrong method on an appraisal is 405 with Allow", web.is("DELETE /api/v1/appraisals/a1 HTTP/1.1\r\n\r\n", web.head("405 Method Not Allowed", "30", "Allow: GET, HEAD\r\n") ++ "{\"error\":\"method_not_allowed\"}")},
   Check{"a path with an extra segment is 404", web.is("GET /api/v1/appraisals/a1/x HTTP/1.1\r\n\r\n", web.head("404 Not Found", "21", "") ++ "{\"error\":\"not_found\"}")},
   Check{"replay applies good lines, counts bad ones and a torn one", web.replayed(St.Replay.finish(web.replay()))},
   Check{"replay notices a torn last line", St.Replay.torn(web.replay())},
   Check{"replay skips the lines a snapshot already holds", web.skipped(St.Replay.feed(web.ascii(web.log()), St.Replay.start(1n, St.Store.empty())))},
   Check{"a snapshot reads back", web.snap(St.Snapshot.parse(St.Snapshot.text(7n, web.two())))},
   Check{"a snapshot cut short doesn't read", Bool.not(Maybe.is_some(&2, St.Snap, St.Snapshot.parse(String.take(St.Snapshot.text(7n, web.two()), 40n))))},
   Check{"UTF-8 bytes decode to characters", WJ.Text.same(U.Utf8.decode([99, 97, 102, 195, 169, 240, 159, 152, 128]), "caf\u{e9}\u{1f600}")},
   Check{"a bad or cut-off UTF-8 byte becomes U+FFFD", WJ.Text.same(U.Utf8.decode([97, 255, 98, 195]), "a\u{fffd}b\u{fffd}")},
   Check{"a request with no body is whole once its headers end", Bool.and(WA.Http.ready(web.ascii("GET / HTTP/1.1\r\n\r\n")), Bool.not(WA.Http.ready(web.ascii("GET / HTTP/1.1\r\nHost: x\r\n"))))},
   Check{"a request with a body waits for Content-Length bytes", Bool.and(WA.Http.ready(web.ascii("POST / HTTP/1.1\r\ncontent-length: 2\r\n\r\nab")), Bool.not(WA.Http.ready(web.ascii("POST / HTTP/1.1\r\nContent-Length: 2\r\n\r\na"))))},
   Check{"Content-Length counts bytes, not characters", Bool.and(WA.Http.ready(web.sized([195, 169])), Bool.not(WA.Http.ready(web.sized([195]))))},
   Check{"the spec is OpenAPI 3.1", String.starts_with(WO.Spec.text(), "{\n  \"openapi\": \"3.1.0\",")}]

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
  +all = List.append(&2, Check, geo_checks(), List.append(&2, Check, times_checks(), List.append(&2, Check, load_checks(), List.append(&2, Check, nation_checks(), List.append(&2, Check, base_checks(), List.append(&2, Check, solve_checks(), List.append(&2, Check, heal_checks(), List.append(&2, Check, road_checks(), web_checks()))))))))
  IO.bind(Unit, Unit, print_all(all), u => finish(failed(all)))
