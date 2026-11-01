import Base
import ./types.bend as T
import ./jobs.bend as J
import ./route.bend as R

# A plan's validity, as one Bool that runs in production and in the browser.

type Slot is Data:
  Slot{crew: Nat, day: Nat}

def Route.slot(+r: T.Route) -> Slot:
  Slot{T.Contractor.id(T.Route.crew(r)), T.Route.day(r)}

def Routes.slots(routes: List<&2, T.Route>) -> List<&2, Slot>:
  match routes:
    case Nil{}:
      Nil{}
    case r <> t:
      Route.slot(r) <> Routes.slots(t)

# Slots run in strict order by crew, then day.
def Slot.lt(a: Slot, b: Slot) -> Bool:
  match a b:
    case Slot{+c1, +d1} Slot{+c2, +d2}:
      Bool.or(Nat.is_lt(c1, c2), Bool.and(Nat.is_eq(c1, c2), Nat.is_lt(d1, d2)))

def Slot.is_eq(a: Slot, b: Slot) -> Bool:
  match a b:
    case Slot{c1, d1} Slot{c2, d2}:
      Bool.and(Nat.is_eq(c1, c2), Nat.is_eq(d1, d2))

def Slots.after(xs: List<&2, Slot>, +lo: Slot) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case +h <> t:
      Bool.and(Slot.lt(lo, h), Slots.after(t, h))

def Slots.sorted(xs: List<&2, Slot>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case +h <> t:
      Slots.after(t, h)

def Crews.has(crews: List<&2, T.Contractor>, +c: T.Contractor) -> Bool:
  match crews:
    case Nil{}:
      False{}
    case h <> t:
      Bool.or(T.Contractor.is_eq(h, c), Crews.has(t, c))

def Routes.jobs(routes: List<&2, T.Route>) -> List<&2, T.Appraisal>:
  match routes:
    case Nil{}:
      Nil{}
    case r <> t:
      List.append(&2, T.Appraisal, R.Stops.jobs(T.Route.stops(r)), Routes.jobs(t))

def Exceptions.jobs(xs: List<&2, T.Exception>) -> List<&2, T.Appraisal>:
  match xs:
    case Nil{}:
      Nil{}
    case e <> t:
      T.Exception.job(e) <> Exceptions.jobs(t)

# Everything the plan has a place for: on a route, in the backlog, or in the
# exceptions queue.
def Plan.placed(+plan: T.Plan) -> List<&2, T.Appraisal>:
  List.append(&2, T.Appraisal, Routes.jobs(T.Plan.routes(plan)),
    List.append(&2, T.Appraisal, T.Plan.backlog(plan), Exceptions.jobs(T.Plan.exceptions(plan))))

def Route.fine(+crews: List<&2, T.Contractor>, +cap: Nat, +r: T.Route) -> Bool:
  Bool.and(Crews.has(crews, T.Route.crew(r)), R.Route.ok(cap, r))

def Routes.ok(routes: List<&2, T.Route>, +crews: List<&2, T.Contractor>, +cap: Nat) -> Bool:
  match routes:
    case Nil{}:
      True{}
    case +r <> t:
      Bool.and(Route.fine(crews, cap, r), Routes.ok(t, crews, cap))

def Routes.locked(routes: List<&2, T.Route>) -> List<&2, List<&2, T.Stop>>:
  match routes:
    case Nil{}:
      Nil{}
    case r <> t:
      R.Stops.locked(T.Route.stops(r)) <> Routes.locked(t)

def Instance.ok(+inst: T.Instance) -> Bool:
  J.rising(T.Instance.jobs(inst), 0n)

def Plan.partition_ok(+inst: T.Instance, +plan: T.Plan) -> Bool:
  J.same(J.sort(Plan.placed(plan)), T.Instance.jobs(inst))

def Plan.valid(+inst: T.Instance, +plan: T.Plan) -> Bool:
  Bool.and(Instance.ok(inst),
    Bool.and(Plan.partition_ok(inst, plan),
      Bool.and(Slots.sorted(Routes.slots(T.Plan.routes(plan))),
        Routes.ok(T.Plan.routes(plan), T.Instance.crews(inst), T.Instance.cap(inst)))))

# Everything waits in the backlog. Always available, so a planner that goes
# wrong can fall back to it.
def Plan.trivial(+inst: T.Instance) -> T.Plan:
  T.Plan{Nil{}, T.Instance.jobs(inst), Nil{}}

# The parallel checker
# --------------------

# Splits the routes in half level by level. Routes cost about the same to check,
# so halves by count are balanced.
def Routes.ok_par(+fuel: Nat, +size: Nat, +routes: List<&2, T.Route>, +crews: List<&2, T.Contractor>, +cap: Nat) -> Bool:
  match fuel:
    case 0n:
      Routes.ok(routes, crews, cap)
    case 1n+f:
      +half = Nat.div(size, 2n)
      a b = Routes.ok_par(f, half, List.take(&2, T.Route, routes, half), crews, cap) Routes.ok_par(f, Nat.sub(size, half), List.drop(&2, T.Route, routes, half), crews, cap)
      Bool.and(a, b)

# The same answer as Plan.valid, on every core.
def Plan.check(+inst: T.Instance, +plan: T.Plan) -> Bool:
  +routes = T.Plan.routes(plan)
  +size = List.length(&2, T.Route, routes)
  a b = Plan.partition_ok(inst, plan) Routes.ok_par(5n, size, routes, T.Instance.crews(inst), T.Instance.cap(inst))
  Bool.and(Instance.ok(inst), Bool.and(a, Bool.and(Slots.sorted(Routes.slots(routes)), b)))
