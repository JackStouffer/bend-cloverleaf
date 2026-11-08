import Base
import ../core/types.bend as T
import ../core/times.bend as Tm
import ../core/route.bend as R
import ../core/heal.bend as H
import ../core/solve.bend as S

# Two simple planners for the benchmark to beat. Neither leaves a contractor's
# zips, and each adds a stop to the end of a route and never reorders it.
#
#   first_fit  tightest deadline first, onto the first route with room: the
#              lowest contractor id, then the earliest day
#   nearest    in arrival order, onto the nearest contractor with room, on
#              the earliest day
#
# Both publish through the proven checker, like the real planner.

type Choice is Data:
  Choice{crew: Nat, day: Nat, score: Nat}

def Choice.score(c: Choice) -> Nat:
  match c:
    case Choice{a, b, s}:
      s

def Choice.pick(c: Bool, x: Choice, y: Choice) -> Choice:
  match c:
    case True{}:
      y
    case False{}:
      x

# The lower score wins, and the earlier route wins a tie.
def better(a: Maybe<&2, Choice>, b: Maybe<&2, Choice>) -> Maybe<&2, Choice>:
  match a b:
    case None{} _:
      b
    case Some{x} None{}:
      Some{x}
    case Some{+x} Some{+y}:
      Some{Choice.pick(Nat.is_lt(Choice.score(y), Choice.score(x)), x, y)}

def make(c: Bool, +crew: Nat, +day: Nat, +score: Nat) -> Maybe<&2, Choice>:
  match c:
    case True{}:
      Some{Choice{crew, day, score}}
    case False{}:
      None{}

def one(+times: T.Times, +job: T.Appraisal, +nearest: Bool, +r: T.Route) -> Maybe<&2, Choice>:
  +crew = T.Route.crew(r)
  +home = T.Contractor.home(crew)
  +site = T.Appraisal.site(job)
  +added = S.detour(times, S.last_site(T.Route.stops(r), home), site, home)
  +ok = Bool.and(R.Nats.has(T.Contractor.zips(crew), T.Appraisal.zip(job)), S.Select.fits(r, job, added))
  make(ok, T.Contractor.id(crew), T.Route.day(r), Bool.pick(Nat, nearest, Tm.minutes(times, home, site), 0n))

def scan(routes: List<&2, T.Route>, +times: T.Times, +job: T.Appraisal, +nearest: Bool) -> Maybe<&2, Choice>:
  match routes:
    case Nil{}:
      None{}
    case r <> t:
      better(one(times, job, nearest, r), scan(t, times, job, nearest))

type Acc is Data:
  Acc{routes: List<&2, T.Route>, backlog: List<&2, T.Appraisal>, exceptions: List<&2, T.Exception>}

def Acc.routes(a: Acc) -> List<&2, T.Route>:
  match a:
    case Acc{r, b, e}:
      r

def hold(urgent: Bool, +job: T.Appraisal, acc: Acc) -> Acc:
  match urgent acc:
    case True{} Acc{r, b, e}:
      Acc{r, b, T.Exception{job, T.NoCapacity{}} <> e}
    case False{} Acc{r, b, e}:
      Acc{r, job <> b, e}

def put(c: Choice, +times: T.Times, +cap: Nat, +job: T.Appraisal, acc: Acc) -> Acc:
  match c acc:
    case Choice{crew, day, _} Acc{rs, b, e}:
      +ed = H.Routes.put(rs, times, cap, crew, day, job, 1000000n)
      Acc{H.Edited.routes(ed), List.append(&2, T.Appraisal, R.Stops.jobs(H.Edited.shed(ed)), b), e}

def step(m: Maybe<&2, Choice>, +times: T.Times, +cap: Nat, +last: Nat, +job: T.Appraisal, acc: Acc) -> Acc:
  match m:
    case Some{c}:
      put(c, times, cap, job, acc)
    case None{}:
      hold(Nat.is_lt(T.Appraisal.due(job), last), job, acc)

def assign(jobs: List<&2, T.Appraisal>, +times: T.Times, +cap: Nat, +nearest: Bool, +last: Nat, +acc: Acc) -> Acc:
  match jobs:
    case Nil{}:
      acc
    case +j <> t:
      assign(t, times, cap, nearest, last, step(scan(Acc.routes(acc), times, j, nearest), times, cap, last, j, acc))

def Acc.plan(a: Acc) -> T.Plan:
  match a:
    case Acc{r, b, e}:
      T.Plan{r, b, e}

def run(+inst: T.Instance, +jobs: List<&2, T.Appraisal>, +nearest: Bool, +first: Nat, +last: Nat) -> T.Plan:
  +times = T.Instance.times(inst)
  +routes = S.blank(times, T.Instance.crews(inst), first, last)
  S.publish(inst, Acc.plan(assign(jobs, times, T.Instance.cap(inst), nearest, last, Acc{routes, Nil{}, Nil{}})))

def first_fit(+inst: T.Instance, +first: Nat, +last: Nat) -> T.Plan:
  run(inst, List.sort(~T.Appraisal, ~S.by_due, T.Instance.jobs(inst)), False{}, first, last)

def nearest(+inst: T.Instance, +first: Nat, +last: Nat) -> T.Plan:
  run(inst, T.Instance.jobs(inst), True{}, first, last)
