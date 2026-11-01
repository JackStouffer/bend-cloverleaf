import Base
import ./types.bend as T
import ./lifecycle.bend as Life
import ./jobs.bend as J
import ./route.bend as R
import ./plan.bend as P

# Changing a plan while it's being worked. Each edit touches the locked head of a
# route only through a lifecycle action, and rebuilds the route through
# Route.remake, so what comes out is valid by construction.

type Edit is Data:
  Pull{id: Nat}
  Clear{crew: Nat, day: Nat}
  Reorder{crew: Nat, day: Nat, tail: List<&2, T.Stop>}
  Begin{id: Nat}
  Finish{id: Nat}
  Abandon{id: Nat}

def Route.at(+r: T.Route, +c: Nat, +d: Nat) -> Bool:
  Bool.and(Nat.is_eq(T.Contractor.id(T.Route.crew(r)), c), Nat.is_eq(T.Route.day(r), d))

# Rebuilds r, adding `out` to what the rebuild sheds.
def Route.reshape(+cap: Nat, +r: T.Route, closed: Bool, +h: List<&2, T.Stop>, +t: List<&2, T.Stop>, out: List<&2, T.Stop>) -> R.Step:
  R.Step.add(out, R.Route.remake(cap, T.Route.crew(r), T.Route.day(r), closed, h, t))

def Stop.start(s: T.Stop) -> T.Stop:
  match s:
    case T.Stop{j, +t}:
      T.Stop{j, Life.advance(t, Life.Start{})}

def Stops.start(xs: List<&2, T.Stop>) -> List<&2, T.Stop>:
  match xs:
    case Nil{}:
      Nil{}
    case s <> t:
      Stop.start(s) <> Stops.start(t)

def Stop.finish.if(c: Bool, s: T.Stop) -> T.Stop:
  match c:
    case True{}:
      T.Stop{T.Stop.job(s), T.Completed{}}
    case False{}:
      s

def Stops.finish(xs: List<&2, T.Stop>, +i: Nat) -> List<&2, T.Stop>:
  match xs:
    case Nil{}:
      Nil{}
    case +s <> t:
      Stop.finish.if(R.Test.run(R.IsUnderway{i}, s), s) <> Stops.finish(t, i)

# The same appraisals in another order, all still open.
def Stops.same_bag(+xs: List<&2, T.Stop>, +ys: List<&2, T.Stop>) -> Bool:
  Bool.and(R.Stops.all_open(xs), J.same(J.sort(R.Stops.jobs(xs)), J.sort(R.Stops.jobs(ys))))

def Route.h(+r: T.Route) -> List<&2, T.Stop>:
  R.Stops.head(T.Route.stops(r))

def Route.t(+r: T.Route) -> List<&2, T.Stop>:
  R.Stops.tail(T.Route.stops(r))

# Each edit is guarded by a Bool, so a route it doesn't touch costs no rebuild.
def Pull.if(c: Bool, +cap: Nat, +r: T.Route, +i: Nat) -> R.Step:
  match c:
    case True{}:
      Route.reshape(cap, r, T.Route.closed(r), Route.h(r), R.Stops.cut(Route.t(r), R.HasId{i}), R.Stops.keep(Route.t(r), R.HasId{i}))
    case False{}:
      R.Step{r, Nil{}}

def Clear.if(c: Bool, +cap: Nat, +r: T.Route) -> R.Step:
  match c:
    case True{}:
      Route.reshape(cap, r, True{}, Route.h(r), Nil{}, Route.t(r))
    case False{}:
      R.Step{r, Nil{}}

def Reorder.if(c: Bool, +cap: Nat, +r: T.Route, +n: List<&2, T.Stop>) -> R.Step:
  match c:
    case True{}:
      Route.reshape(cap, r, T.Route.closed(r), Route.h(r), n, Nil{})
    case False{}:
      R.Step{r, Nil{}}

def Begin.if(c: Bool, +cap: Nat, +r: T.Route, +i: Nat) -> R.Step:
  match c:
    case True{}:
      Route.reshape(cap, r, T.Route.closed(r), R.Stops.append(Route.h(r), Stops.start(R.Stops.keep(Route.t(r), R.HasId{i}))), R.Stops.cut(Route.t(r), R.HasId{i}), Nil{})
    case False{}:
      R.Step{r, Nil{}}

def Finish.if(c: Bool, +cap: Nat, +r: T.Route, +i: Nat) -> R.Step:
  match c:
    case True{}:
      Route.reshape(cap, r, T.Route.closed(r), Stops.finish(Route.h(r), i), Route.t(r), Nil{})
    case False{}:
      R.Step{r, Nil{}}

def Abandon.if(c: Bool, +cap: Nat, +r: T.Route, +i: Nat) -> R.Step:
  match c:
    case True{}:
      Route.reshape(cap, r, T.Route.closed(r), R.Stops.cut(Route.h(r), R.IsUnderway{i}), Route.t(r), R.Stops.keep(Route.h(r), R.IsUnderway{i}))
    case False{}:
      R.Step{r, Nil{}}

def Route.apply(+cap: Nat, e: Edit, +r: T.Route) -> R.Step:
  match e:
    case Pull{+i}:
      Pull.if(R.Stops.any(Route.t(r), R.HasId{i}), cap, r, i)
    case Clear{+c, +d}:
      Clear.if(Route.at(r, c, d), cap, r)
    case Reorder{+c, +d, +n}:
      Reorder.if(Bool.and(Route.at(r, c, d), Stops.same_bag(n, Route.t(r))), cap, r, n)
    case Begin{+i}:
      Begin.if(R.Stops.any(Route.t(r), R.HasId{i}), cap, r, i)
    case Finish{+i}:
      Finish.if(R.Stops.any(Route.h(r), R.IsUnderway{i}), cap, r, i)
    case Abandon{+i}:
      Abandon.if(R.Stops.any(Route.h(r), R.IsUnderway{i}), cap, r, i)

type Edited is Data:
  Edited{routes: List<&2, T.Route>, shed: List<&2, T.Stop>}

def Edited.routes(e: Edited) -> List<&2, T.Route>:
  match e:
    case Edited{r, s}:
      r

def Edited.shed(e: Edited) -> List<&2, T.Stop>:
  match e:
    case Edited{r, s}:
      s

def Edited.cons(s: R.Step, e: Edited) -> Edited:
  match s e:
    case R.Step{r, x} Edited{rs, xs}:
      Edited{r <> rs, R.Stops.append(x, xs)}

def Routes.apply(routes: List<&2, T.Route>, +cap: Nat, +e: Edit) -> Edited:
  match routes:
    case Nil{}:
      Edited{Nil{}, Nil{}}
    case r <> t:
      Edited.cons(Route.apply(cap, e, r), Routes.apply(t, cap, e))

def Plan.with(routes: List<&2, T.Route>, shed: List<&2, T.Stop>, backlog: List<&2, T.Appraisal>, ex: List<&2, T.Exception>) -> T.Plan:
  T.Plan{routes, List.append(&2, T.Appraisal, R.Stops.jobs(shed), backlog), ex}

def Plan.edit(+cap: Nat, +e: Edit, +plan: T.Plan) -> T.Plan:
  +done = Routes.apply(T.Plan.routes(plan), cap, e)
  Plan.with(Edited.routes(done), Edited.shed(done), T.Plan.backlog(plan), T.Plan.exceptions(plan))

# Whether a stop on the plan is locked, which is what refuses a cancellation.
def Routes.locks(routes: List<&2, T.Route>, +i: Nat) -> Bool:
  match routes:
    case Nil{}:
      False{}
    case r <> t:
      Bool.or(R.Stops.any(R.Stops.head(T.Route.stops(r)), R.HasId{i}), Routes.locks(t, i))

def Exceptions.without.put(c: Bool, e: T.Exception, r: List<&2, T.Exception>) -> List<&2, T.Exception>:
  match c:
    case True{}:
      r
    case False{}:
      e <> r

def Exceptions.without(xs: List<&2, T.Exception>, +i: Nat) -> List<&2, T.Exception>:
  match xs:
    case Nil{}:
      Nil{}
    case +h <> t:
      Exceptions.without.put(Nat.is_eq(T.Appraisal.id(T.Exception.job(h)), i), h, Exceptions.without(t, i))

# Inserting at a position in the tail. Past the end means the end.
def Stops.insert_at(xs: List<&2, T.Stop>, at: Nat, s: T.Stop) -> List<&2, T.Stop>:
  match xs at:
    case Nil{} _:
      [s]
    case h <> t 0n:
      s <> h <> t
    case h <> t 1n+p:
      h <> Stops.insert_at(t, p, s)

def Route.put(+cap: Nat, +r: T.Route, +job: T.Appraisal, at: Nat) -> R.Step:
  +stops = T.Route.stops(r)
  Route.reshape(cap, r, T.Route.closed(r), R.Stops.head(stops),
    Stops.insert_at(R.Stops.tail(stops), at, T.Stop{job, T.Open{}}), Nil{})

def Routes.put.if(m: Bool, +r: T.Route, +t: List<&2, T.Route>, +cap: Nat, +job: T.Appraisal, +at: Nat, rest: Edited) -> Edited:
  match m:
    case True{}:
      Edited.cons(Route.put(cap, r, job, at), Edited{t, Nil{}})
    case False{}:
      Edited.cons(R.Step{r, Nil{}}, rest)

def Routes.put(routes: List<&2, T.Route>, +cap: Nat, +c: Nat, +d: Nat, +job: T.Appraisal, +at: Nat) -> Edited:
  match routes:
    case Nil{}:
      Edited{Nil{}, Nil{}}
    case +r <> +t:
      Routes.put.if(Route.at(r, c, d), r, t, cap, job, at, Routes.put(t, cap, c, d, job, at))

def Routes.open_at.if(m: Bool, closed: Bool, rest: Bool) -> Bool:
  match m:
    case True{}:
      Bool.not(closed)
    case False{}:
      rest

# Whether the first route in this slot exists and takes new work.
def Routes.open_at(routes: List<&2, T.Route>, +c: Nat, +d: Nat) -> Bool:
  match routes:
    case Nil{}:
      False{}
    case +r <> t:
      Routes.open_at.if(Route.at(r, c, d), T.Route.closed(r), Routes.open_at(t, c, d))

type Change is Data:
  Cancel{id: Nat}
  Request{job: T.Appraisal}
  Sick{crew: Nat, day: Nat}
  Improve{crew: Nat, day: Nat, tail: List<&2, T.Stop>}
  Release{id: Nat}
  Backfill{id: Nat, crew: Nat, day: Nat, at: Nat}

type Progress is Data:
  Started{id: Nat}
  Finished{id: Nat}
  Missed{id: Nat}

type State is Data:
  State{inst: T.Instance, plan: T.Plan}

def State.inst(s: State) -> T.Instance:
  match s:
    case State{i, p}:
      i

def State.plan(s: State) -> T.Plan:
  match s:
    case State{i, p}:
      p

def Instance.without(+inst: T.Instance, +i: Nat) -> T.Instance:
  T.Instance{T.Instance.crews(inst), J.without(T.Instance.jobs(inst), i), T.Instance.cap(inst), T.Instance.state(inst)}

def Instance.with(+inst: T.Instance, +job: T.Appraisal) -> T.Instance:
  T.Instance{T.Instance.crews(inst), J.insert(T.Instance.jobs(inst), job), T.Instance.cap(inst), T.Instance.state(inst)}

def Plan.forget(+plan: T.Plan, +i: Nat) -> T.Plan:
  T.Plan{T.Plan.routes(plan), J.without(T.Plan.backlog(plan), i), Exceptions.without(T.Plan.exceptions(plan), i)}

def cancel.if(locked: Bool, +inst: T.Instance, +plan: T.Plan, +i: Nat) -> State:
  match locked:
    case True{}:
      State{inst, plan}
    case False{}:
      State{Instance.without(inst, i), Plan.forget(Plan.edit(T.Instance.cap(inst), Pull{i}, plan), i)}

# Refused once work has started: a locked stop can't leave its route.
def cancel(+inst: T.Instance, +plan: T.Plan, +i: Nat) -> State:
  cancel.if(Routes.locks(T.Plan.routes(plan), i), inst, plan, i)

def request.place(here: Bool, +inst: T.Instance, +plan: T.Plan, +job: T.Appraisal) -> State:
  match here:
    case True{}:
      State{Instance.with(inst, job), T.Plan{T.Plan.routes(plan), job <> T.Plan.backlog(plan), T.Plan.exceptions(plan)}}
    case False{}:
      State{inst, plan}

def request.if(known: Bool, +inst: T.Instance, +plan: T.Plan, +job: T.Appraisal) -> State:
  match known:
    case True{}:
      State{inst, plan}
    case False{}:
      request.place(Nat.is_eq(T.Appraisal.state(job), T.Instance.state(inst)), inst, plan, job)

# Retries are safe: an id already known changes nothing. A request from another
# state changes nothing either, because it belongs to that state's instance.
def request(+inst: T.Instance, +plan: T.Plan, +job: T.Appraisal) -> State:
  request.if(J.has_id(T.Instance.jobs(inst), T.Appraisal.id(job)), inst, plan, job)

def backfill.put(+cap: Nat, +plan: T.Plan, rest: List<&2, T.Appraisal>, +job: T.Appraisal, +c: Nat, +d: Nat, +at: Nat) -> T.Plan:
  +done = Routes.put(T.Plan.routes(plan), cap, c, d, job, at)
  Plan.with(Edited.routes(done), Edited.shed(done), rest, T.Plan.exceptions(plan))

def backfill.check(ok: Bool, +cap: Nat, +plan: T.Plan, rest: List<&2, T.Appraisal>, +job: T.Appraisal, +c: Nat, +d: Nat, +at: Nat) -> T.Plan:
  match ok:
    case True{}:
      backfill.put(cap, plan, rest, job, c, d, at)
    case False{}:
      plan

def backfill.go(+cap: Nat, +plan: T.Plan, found: Maybe<&2, T.Appraisal>, rest: List<&2, T.Appraisal>, +c: Nat, +d: Nat, +at: Nat) -> T.Plan:
  match found:
    case None{}:
      plan
    case Some{+job}:
      backfill.check(Routes.open_at(T.Plan.routes(plan), c, d), cap, plan, rest, job, c, d, at)

# Moves one appraisal from the backlog onto an open route.
def backfill(+cap: Nat, +plan: T.Plan, +i: Nat, +c: Nat, +d: Nat, +at: Nat) -> T.Plan:
  +taken = J.take(T.Plan.backlog(plan), i)
  backfill.go(cap, plan, J.Taken.found(taken), J.Taken.rest(taken), c, d, at)

def State.edit(+st: State, +e: Edit) -> State:
  State{State.inst(st), Plan.edit(T.Instance.cap(State.inst(st)), e, State.plan(st))}

def Heal.apply(+st: State, ev: Change) -> State:
  match ev:
    case Cancel{i}:
      cancel(State.inst(st), State.plan(st), i)
    case Request{job}:
      request(State.inst(st), State.plan(st), job)
    case Sick{c, d}:
      State.edit(st, Clear{c, d})
    case Improve{c, d, n}:
      State.edit(st, Reorder{c, d, n})
    case Release{i}:
      State.edit(st, Pull{i})
    case Backfill{i, c, d, at}:
      State{State.inst(st), backfill(T.Instance.cap(State.inst(st)), State.plan(st), i, c, d, at)}

def Heal.run(evs: List<&2, Change>, +st: State) -> State:
  match evs:
    case Nil{}:
      st
    case e <> t:
      Heal.run(t, Heal.apply(st, e))

def Progress.apply(+st: State, ev: Progress) -> State:
  match ev:
    case Started{i}:
      State.edit(st, Begin{i})
    case Finished{i}:
      State.edit(st, Finish{i})
    case Missed{i}:
      State.edit(st, Abandon{i})
