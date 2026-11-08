import Base
import ../core/types.bend as T
import ../core/route.bend as R
import ../core/solve.bend as S

# What the benchmark reports about a state's plan. Pure, so the scenarios check
# the numbers the benchmark prints.
#
# feasible counts urgent appraisals left off the routes that could still go on
# one: the planner's own search, in zip or out within the cap, finds a place for
# them in the finished plan. A deadline missed that way was a feasible deadline.

type Stats is Data:
  Stats{routes: Nat, used: Nat, placed: Nat, backlog: Nat, exceptions: Nat, late: Nat, outside: Nat,
    drive: Nat, worked: Nat, peak: Nat, sq: Nat, feasible: Nat, impossible: Nat, crews: Nat, wsq: Nat, wpeak: Nat}

def Stats.zero() -> Stats:
  Stats{0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n}

def Stats.add(a: Stats, b: Stats) -> Stats:
  match a b:
    case Stats{r1, u1, p1, b1, e1, l1, o1, d1, w1, k1, s1, f1, i1, c1, q1, m1} Stats{r2, u2, p2, b2, e2, l2, o2, d2, w2, k2, s2, f2, i2, c2, q2, m2}:
      Stats{Nat.add(r1, r2), Nat.add(u1, u2), Nat.add(p1, p2), Nat.add(b1, b2), Nat.add(e1, e2), Nat.add(l1, l2),
        Nat.add(o1, o2), Nat.add(d1, d2), Nat.add(w1, w2), Nat.max(k1, k2), Nat.add(s1, s2), Nat.add(f1, f2), Nat.add(i1, i2), Nat.add(c1, c2), Nat.add(q1, q2), Nat.max(m1, m2)}

def Stats.placed(s: Stats) -> Nat:
  match s:
    case Stats{r, u, p, b, e, l, o, d, w, k, q, f, i, c, x, m}:
      p

def Stats.drive(s: Stats) -> Nat:
  match s:
    case Stats{r, u, p, b, e, l, o, d, w, k, q, f, i, c, x, m}:
      d

def Stats.peak(s: Stats) -> Nat:
  match s:
    case Stats{r, u, p, b, e, l, o, d, w, k, q, f, i, c, x, m}:
      k

def Stats.feasible(s: Stats) -> Nat:
  match s:
    case Stats{r, u, p, b, e, l, o, d, w, k, q, f, i, c, x, m}:
      f

def Stats.impossible(s: Stats) -> Nat:
  match s:
    case Stats{r, u, p, b, e, l, o, d, w, k, q, f, i, c, x, m}:
      i

def bit(c: Bool) -> Nat:
  U32.to_nat(Bool.to_u32(c))

def Route.stats(+times: T.Times, +r: T.Route) -> Stats:
  +a = T.Route.audit(r)
  +stops = T.Route.stops(r)
  +n = List.length(&2, T.Stop, stops)
  +w = T.Audit.minutes(a)
  Stats{1n, bit(Nat.is_gt(n, 0n)), n, 0n, 0n, List.length(&2, Nat, T.Audit.late(a)), List.length(&2, Nat, T.Audit.outside(a)),
    R.Route.loop_drive(times, T.Route.crew(r), stops), w, w, Nat.mul(w, w), 0n, 0n, 0n, 0n, 0n}

def Routes.stats(routes: List<&2, T.Route>, +times: T.Times) -> Stats:
  match routes:
    case Nil{}:
      Stats.zero()
    case +r <> t:
      Stats.add(Route.stats(times, r), Routes.stats(t, times))

# Each contractor's minutes over the whole horizon. Routes run in slot order, so
# a contractor's routes are next to each other.
def Week.close(+w: Nat) -> Stats:
  Stats{0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 1n, Nat.mul(w, w), w}

# The contractor whose week is being added up, the minutes so far, and the
# weeks already closed.
type Week is Data:
  Week{crew: Nat, minutes: Nat, done: Stats}

def Week.next(same: Bool, +c: Nat, +m: Nat, +crew: Nat, +w: Nat, done: Stats) -> Week:
  match same:
    case True{}:
      Week{crew, Nat.add(w, m), done}
    case False{}:
      Week{c, m, Stats.add(done, Week.close(w))}

def Week.step(+r: T.Route, a: Week) -> Week:
  match a:
    case Week{+crew, +w, done}:
      +c = T.Contractor.id(T.Route.crew(r))
      Week.next(Nat.is_eq(c, crew), c, T.Audit.minutes(T.Route.audit(r)), crew, w, done)

def Week.go(routes: List<&2, T.Route>, a: Week) -> Stats:
  match routes:
    case Nil{}:
      match a:
        case Week{_, +w, done}:
          Stats.add(done, Week.close(w))
    case +r <> t:
      Week.go(t, Week.step(r, a))

def Weeks.stats(routes: List<&2, T.Route>) -> Stats:
  match routes:
    case Nil{}:
      Stats.zero()
    case +r <> t:
      Week.go(t, Week{T.Contractor.id(T.Route.crew(r)), T.Audit.minutes(T.Route.audit(r)), Stats.zero()})

def Stats.crews(s: Stats) -> Nat:
  match s:
    case Stats{r, u, p, b, e, l, o, d, w, k, q, f, i, c, x, m}:
      c

def Stats.wpeak(s: Stats) -> Nat:
  match s:
    case Stats{r, u, p, b, e, l, o, d, w, k, q, f, i, c, x, m}:
      m

# Whether the job has a place in the finished plan, in zip or out.
def fits(+routes: List<&2, T.Route>, +times: T.Times, +cap: Nat, +job: T.Appraisal) -> Bool:
  Bool.or(Maybe.is_some(&2, S.Cand, S.Select.seq(routes, times, cap, job, False{})),
    Maybe.is_some(&2, S.Cand, S.Select.seq(routes, times, cap, job, True{})))

# Urgent work that wouldn't fit even an empty route, on its own there and back.
# That's no proof it was impossible, because a stop added to a route already
# driving that way costs far less than a trip of its own.
def Impossible.count(xs: List<&2, T.Appraisal>, +empty: List<&2, T.Route>, +times: T.Times, +cap: Nat, +last: Nat) -> Nat:
  match xs:
    case Nil{}:
      0n
    case +j <> t:
      Nat.add(bit(Bool.and(Nat.is_lt(T.Appraisal.due(j), last), Bool.not(fits(empty, times, cap, j)))), Impossible.count(t, empty, times, cap, last))

def Missed.count(xs: List<&2, T.Appraisal>, +routes: List<&2, T.Route>, +times: T.Times, +cap: Nat, +last: Nat) -> Nat:
  match xs:
    case Nil{}:
      0n
    case +j <> t:
      Nat.add(bit(Bool.and(Nat.is_lt(T.Appraisal.due(j), last), fits(routes, times, cap, j))), Missed.count(t, routes, times, cap, last))

def Exceptions.jobs(xs: List<&2, T.Exception>) -> List<&2, T.Appraisal>:
  match xs:
    case Nil{}:
      Nil{}
    case e <> t:
      T.Exception.job(e) <> Exceptions.jobs(t)

# first is the first day planned and last the day after the horizon, so a job due before it is urgent.
def of(+inst: T.Instance, +plan: T.Plan, +first: Nat, +last: Nat) -> Stats:
  +times = T.Instance.times(inst)
  +cap = T.Instance.cap(inst)
  +routes = T.Plan.routes(plan)
  +missed = List.append(&2, T.Appraisal, Exceptions.jobs(T.Plan.exceptions(plan)), T.Plan.backlog(plan))
  Stats.add(Stats.add(Routes.stats(routes, times), Weeks.stats(routes)),
    Stats{0n, 0n, 0n, List.length(&2, T.Appraisal, T.Plan.backlog(plan)), List.length(&2, T.Exception, T.Plan.exceptions(plan)),
      0n, 0n, 0n, 0n, 0n, 0n, Missed.count(missed, routes, times, cap, last),
      Impossible.count(missed, S.blank(times, T.Instance.crews(inst), first, last), times, cap, last), 0n, 0n, 0n})

# Plan files
# ----------

# plan-<planner>.bin, in little-endian U32 words: the route count, then each
# route as contractor id, day, minutes, stop count and the stops' appraisal ids,
# then the backlog's count and ids, then the exceptions' count and ids.
def Ids.stops(xs: List<&2, T.Stop>, rest: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      rest
    case s <> t:
      T.Stop.id(s) <> Ids.stops(t, rest)

def Ids.jobs(xs: List<&2, T.Appraisal>, rest: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      rest
    case j <> t:
      T.Appraisal.id(j) <> Ids.jobs(t, rest)

def Words.routes(rs: List<&2, T.Route>, rest: List<&2, Nat>) -> List<&2, Nat>:
  match rs:
    case Nil{}:
      rest
    case +r <> t:
      +stops = T.Route.stops(r)
      T.Contractor.id(T.Route.crew(r)) <> T.Route.day(r) <> T.Audit.minutes(T.Route.audit(r)) <> List.length(&2, T.Stop, stops) <> Ids.stops(stops, Words.routes(t, rest))

def Plan.words(+plan: T.Plan) -> List<&2, Nat>:
  +routes = T.Plan.routes(plan)
  +backlog = T.Plan.backlog(plan)
  +ex = Exceptions.jobs(T.Plan.exceptions(plan))
  List.length(&2, T.Route, routes) <> Words.routes(routes, List.length(&2, T.Appraisal, backlog) <> Ids.jobs(backlog, List.length(&2, T.Appraisal, ex) <> Ids.jobs(ex, Nil{})))
