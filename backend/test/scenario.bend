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

def job(+id: Nat, +north: Nat, +zip: Nat, +due: Nat) -> T.Appraisal:
  T.Appraisal{id, near_nyc(north), zip, due, 20n}

def crew(+id: Nat, +zips: List<&2, Nat>, +max: Nat) -> T.Contractor:
  T.Contractor{id, nyc(), zips, max, [10n, 11n]}

def inst() -> T.Instance:
  T.Instance{[crew(1n, [100n, 101n], 480n), crew(2n, [102n], 480n)],
    [job(1n, 100n, 100n, 10n), job(2n, 200n, 100n, 10n), job(3n, 300n, 101n, 11n), job(4n, 400n, 102n, 10n)], 60n}

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
    job(5n, 500n, 100n, 20n), job(6n, 600n, 100n, 20n), job(7n, 700n, 100n, 20n), job(8n, 800n, 100n, 20n)], 60n}

# One day with room for about two stops, and the job due first listed last.
def tight_inst() -> T.Instance:
  T.Instance{[crew(1n, [100n], 60n)], [job(1n, 100n, 100n, 30n), job(2n, 200n, 100n, 30n), job(3n, 300n, 100n, 30n), job(4n, 400n, 100n, 10n)], 60n}

# Work nobody covers, due inside the horizon: it should cross a zip and be flagged.
def outside_inst() -> T.Instance:
  T.Instance{[crew(1n, [100n], 480n)], [job(1n, 100n, 555n, 10n)], 60n}

# Same, but too far for the cap.
def too_far_inst() -> T.Instance:
  T.Instance{[crew(1n, [100n], 2000n)], [T.Appraisal{1n, la(), 555n, 10n, 20n}], 60n}

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
   Check{"releasing a stop moves it to the backlog", Nat.is_eq(backlog(after(start(), H.Release{i})), 1n)},
   Check{"backfill moves it onto a route", Nat.is_eq(backlog(after(after(start(), H.Release{i}), H.Backfill{i, 1n, 11n, 0n})), 0n)},
   Check{"backfill keeps the plan valid", valid(after(after(start(), H.Release{i}), H.Backfill{i, 1n, 11n, 0n}))},
   Check{"a sick contractor's open stops go to the backlog", Nat.is_gt(backlog(after(start(), H.Sick{1n, 10n})), 0n)},
   Check{"a sick contractor's plan stays valid", valid(after(start(), H.Sick{1n, 10n}))},
   Check{"a closed route takes no new work", Nat.is_gt(backlog(after(after(start(), H.Sick{1n, 10n}), H.Backfill{i, 1n, 10n, 0n})), 0n)},
   Check{"a reorder that loses a stop is refused", Nat.is_eq(placed(after(start(), H.Improve{1n, 10n, Nil{}})), 4n)},
   Check{"a refused reorder changes nothing", Nat.is_eq(on_routes(after(start(), H.Improve{1n, 10n, Nil{}})), 4n)}]

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
  +all = List.append(&2, Check, geo_checks(), List.append(&2, Check, solve_checks(), heal_checks()))
  IO.bind(Unit, Unit, print_all(all), u => finish(failed(all)))
