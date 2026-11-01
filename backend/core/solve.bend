import Base
import ./types.bend as T
import ./jobs.bend as J
import ./route.bend as R
import ./plan.bend as P
import ./heal.bend as H
import ./geo.bend as Geo

# A small planner on straight-line times. Nothing it does has to be right for the
# plan to be: publish runs the proven checker on what comes out and falls back
# to the trivial plan. Quality is measured by the benchmark, not proven.

type Cand is Data:
  Cand{crew: Nat, day: Nat, at: Nat, cost: Nat}

def Cand.cost(c: Cand) -> Nat:
  match c:
    case Cand{a, b, d, e}:
      e

def Cand.crew(c: Cand) -> Nat:
  match c:
    case Cand{a, b, d, e}:
      a

def Cand.day(c: Cand) -> Nat:
  match c:
    case Cand{a, b, d, e}:
      b

def Cand.at(c: Cand) -> Nat:
  match c:
    case Cand{a, b, d, e}:
      d

# The lower cost wins, and the earlier candidate wins a tie, so the answer can't
# depend on how the search was split.
def Cand.pick(c: Bool, x: Cand, y: Cand) -> Cand:
  match c:
    case True{}:
      y
    case False{}:
      x

def better(a: Maybe<&2, Cand>, b: Maybe<&2, Cand>) -> Maybe<&2, Cand>:
  match a b:
    case None{} _:
      b
    case Some{x} None{}:
      Some{x}
    case Some{+x} Some{+y}:
      Some{Cand.pick(Nat.is_lt(Cand.cost(y), Cand.cost(x)), x, y)}

# Added drive time for visiting `site` between two points.
def detour(+prev: T.Point, +site: T.Point, +next: T.Point) -> Nat:
  Nat.sub(Nat.add(Geo.minutes(prev, site), Geo.minutes(site, next)), Geo.minutes(prev, next))

type Spot is Data:
  Spot{at: Nat, added: Nat}

def Spot.at(s: Spot) -> Nat:
  match s:
    case Spot{a, b}:
      a

def Spot.added(s: Spot) -> Nat:
  match s:
    case Spot{a, b}:
      b

def Spot.pick(c: Bool, x: Spot, y: Spot) -> Spot:
  match c:
    case True{}:
      y
    case False{}:
      x

# The cheapest place in the tail to add a site. `prev` is where the route is
# coming from at position `at`.
def cheapest(tail: List<&2, T.Stop>, +prev: T.Point, +home: T.Point, +site: T.Point, +at: Nat, +best: Spot) -> Spot:
  match tail:
    case Nil{}:
      +added = detour(prev, site, home)
      Spot.pick(Nat.is_lt(added, Spot.added(best)), best, Spot{at, added})
    case s <> r:
      +next = R.Stop.site(s)
      +added = detour(prev, site, next)
      cheapest(r, next, home, site, 1n+at, Spot.pick(Nat.is_lt(added, Spot.added(best)), best, Spot{at, added}))

def last_site(stops: List<&2, T.Stop>, +from: T.Point) -> T.Point:
  match stops:
    case Nil{}:
      from
    case s <> r:
      last_site(r, R.Stop.site(s))

def Select.fits(+r: T.Route, +job: T.Appraisal, added: Nat) -> Bool:
  +total = Nat.add(Nat.add(T.Audit.minutes(T.Route.audit(r)), added), T.Appraisal.minutes(job))
  Bool.and(Bool.not(T.Route.closed(r)),
    Bool.and(Nat.is_le(T.Route.day(r), T.Appraisal.due(job)),
      Nat.is_le(total, T.Contractor.max_minutes(T.Route.crew(r)))))

# Under the cap once this stop is in. In-zip work can't change the answer, so only
# the outside pass pays for this.
def Select.within_cap(+cap: Nat, +r: T.Route, +job: T.Appraisal, +at: Nat) -> Bool:
  +next = H.Stops.insert_at(H.Route.t(r), at, T.Stop{job, T.Open{}})
  Nat.is_le(R.Route.extra(T.Route.crew(r), R.Stops.append(H.Route.h(r), next)), cap)

# Lighter routes cost less, which is what spreads work across contractors.
def Select.make(c: Bool, +r: T.Route, +at: Nat, +added: Nat) -> Maybe<&2, Cand>:
  match c:
    case True{}:
      Some{Cand{T.Contractor.id(T.Route.crew(r)), T.Route.day(r), at,
        Nat.add(added, Nat.div(T.Audit.minutes(T.Route.audit(r)), 8n))}}
    case False{}:
      None{}

def Select.spot(+r: T.Route, +site: T.Point) -> Spot:
  +home = T.Contractor.home(T.Route.crew(r))
  +h = H.Route.h(r)
  +t = H.Route.t(r)
  +start = last_site(h, home)
  cheapest(t, start, home, site, 0n, Spot{0n, 16777215n})

def Select.in(c: Bool, +r: T.Route, +job: T.Appraisal) -> Maybe<&2, Cand>:
  match c:
    case False{}:
      None{}
    case True{}:
      +s = Select.spot(r, T.Appraisal.site(job))
      Select.make(Select.fits(r, job, Spot.added(s)), r, Spot.at(s), Spot.added(s))

def Select.out(c: Bool, +cap: Nat, +r: T.Route, +job: T.Appraisal) -> Maybe<&2, Cand>:
  match c:
    case True{}:
      None{}
    case False{}:
      +s = Select.spot(r, T.Appraisal.site(job))
      Select.make(Bool.and(Select.fits(r, job, Spot.added(s)), Select.within_cap(cap, r, job, Spot.at(s))), r, Spot.at(s), Spot.added(s))

def Select.one.go(+cap: Nat, +job: T.Appraisal, outside: Bool, +r: T.Route, +inzip: Bool) -> Maybe<&2, Cand>:
  match outside:
    case False{}:
      Select.in(inzip, r, job)
    case True{}:
      Select.out(inzip, cap, r, job)

# What placing this job on this route would cost, if it can go there at all.
def Select.one(+cap: Nat, +job: T.Appraisal, +outside: Bool, +r: T.Route) -> Maybe<&2, Cand>:
  Select.one.go(cap, job, outside, r, R.Nats.has(T.Contractor.zips(T.Route.crew(r)), T.Appraisal.zip(job)))

def Select.seq(routes: List<&2, T.Route>, +cap: Nat, +job: T.Appraisal, +outside: Bool) -> Maybe<&2, Cand>:
  match routes:
    case Nil{}:
      None{}
    case r <> t:
      better(Select.one(cap, job, outside, r), Select.seq(t, cap, job, outside))

# Routes as a balanced tree in slot order, so the search forks without copying
# and an update touches one path. top is the largest slot on the left.
type Forest is Data:
  Bare{}
  Leaf{route: T.Route}
  Fork{top: P.Slot, l: Forest, r: Forest}

def Forest.routes(t: Forest) -> List<&2, T.Route>:
  match t:
    case Bare{}:
      Nil{}
    case Leaf{r}:
      [r]
    case Fork{k, l, r}:
      List.append(&2, T.Route, Forest.routes(l), Forest.routes(r))

# The forked search. Below depth d it runs in one lane: a job's search is short,
# so forking down to single routes would spend more than it saves.
def Select.tree(t: Forest, +d: Nat, +cap: Nat, +job: T.Appraisal, +outside: Bool) -> Maybe<&2, Cand>:
  match t:
    case Bare{}:
      None{}
    case Leaf{r}:
      better(Select.one(cap, job, outside, r), None{})
    case Fork{k, l, r}:
      match d:
        case 0n:
          better(Select.tree(l, 0n, cap, job, outside), Select.tree(r, 0n, cap, job, outside))
        case 1n+e:
          a b = Select.tree(l, e, cap, job, outside) Select.tree(r, e, cap, job, outside)
          better(a, b)

# Building the first plan
# -----------------------

def blank.put(c: Bool, +crew: T.Contractor, +d: Nat, rest: List<&2, T.Route>) -> List<&2, T.Route>:
  match c:
    case True{}:
      R.Route.seal(crew, d, Nil{}, False{}) <> rest
    case False{}:
      rest

def blank.days(days: List<&2, Nat>, +crew: T.Contractor, +first: Nat, +last: Nat) -> List<&2, T.Route>:
  match days:
    case Nil{}:
      Nil{}
    case +d <> t:
      blank.put(Bool.and(Nat.is_ge(d, first), Nat.is_lt(d, last)), crew, d, blank.days(t, crew, first, last))

# One empty route for each day each contractor works. Crews and days are sorted,
# so the routes come out in slot order.
def blank(crews: List<&2, T.Contractor>, +first: Nat, +last: Nat) -> List<&2, T.Route>:
  match crews:
    case Nil{}:
      Nil{}
    case +c <> t:
      List.append(&2, T.Route, blank.days(T.Contractor.days(c), c, first, last), blank(t, first, last))

def by_due(a: T.Appraisal, b: T.Appraisal) -> Bool:
  Nat.is_le(T.Appraisal.due(a), T.Appraisal.due(b))

def last_slot(routes: List<&2, T.Route>, +best: P.Slot) -> P.Slot:
  match routes:
    case Nil{}:
      best
    case +r <> t:
      last_slot(t, P.Route.slot(r))

def Forest.join(a: Forest, +k: P.Slot, b: Forest) -> Forest:
  match b:
    case Bare{}:
      a
    case o:
      Fork{k, a, o}

def Forest.chain(routes: List<&2, T.Route>) -> Forest:
  match routes:
    case Nil{}:
      Bare{}
    case +r <> t:
      Forest.join(Leaf{r}, P.Route.slot(r), Forest.chain(t))

def Forest.pick(c: Bool, +routes: List<&2, T.Route>, next: Unit -> Forest) -> Forest:
  match c:
    case True{}:
      Forest.chain(routes)
    case False{}:
      next(Unit{})

def Forest.of(+depth: Nat, +size: Nat, +routes: List<&2, T.Route>) -> Forest:
  match depth:
    case 0n:
      Forest.chain(routes)
    case 1n+e:
      +half = Nat.div(size, 2n)
      +left = List.take(&2, T.Route, routes, half)
      Forest.pick(Nat.is_le(size, 1n), routes, u => Fork{last_slot(left, P.Slot{0n, 0n}), Forest.of(e, half, left), Forest.of(e, Nat.sub(size, half), List.drop(&2, T.Route, routes, half))})

type Placed is Data:
  Placed{tree: Forest, shed: List<&2, T.Stop>}

def Placed.left(+k: P.Slot, p: Placed, r: Forest) -> Placed:
  match p:
    case Placed{t, x}:
      Placed{Fork{k, t, r}, x}

def Placed.right(+k: P.Slot, l: Forest, p: Placed) -> Placed:
  match p:
    case Placed{t, x}:
      Placed{Fork{k, l, t}, x}

def Leaf.put(c: Bool, +cap: Nat, +job: T.Appraisal, +at: Nat, +r: T.Route) -> Placed:
  match c:
    case True{}:
      +step = H.Route.put(cap, r, job, at)
      Placed{Leaf{R.Step.route(step)}, R.Step.shed(step)}
    case False{}:
      Placed{Leaf{r}, Nil{}}

def Forest.go(c: Bool, a: Unit -> Placed, b: Unit -> Placed) -> Placed:
  match c:
    case True{}:
      a(Unit{})
    case False{}:
      b(Unit{})

def Forest.put(+t: Forest, +slot: P.Slot, +cap: Nat, +job: T.Appraisal, +at: Nat) -> Placed:
  match t:
    case Bare{}:
      Placed{Bare{}, Nil{}}
    case Leaf{+r}:
      Leaf.put(P.Slot.is_eq(P.Route.slot(r), slot), cap, job, at, r)
    case Fork{+k, +l, +r}:
      Forest.go(P.Slot.lt(k, slot),
        u => Placed.right(k, l, Forest.put(r, slot, cap, job, at)),
        u => Placed.left(k, Forest.put(l, slot, cap, job, at), r))

def Cand.slot(+c: Cand) -> P.Slot:
  P.Slot{Cand.crew(c), Cand.day(c)}

type Work is Data:
  Work{tree: Forest, backlog: List<&2, T.Appraisal>, exceptions: List<&2, T.Exception>}

def Work.tree(w: Work) -> Forest:
  match w:
    case Work{t, b, e}:
      t

def Work.done(p: Placed, b: List<&2, T.Appraisal>, e: List<&2, T.Exception>) -> Work:
  match p:
    case Placed{t, x}:
      Work{t, List.append(&2, T.Appraisal, R.Stops.jobs(x), b), e}

def place.apply(+cap: Nat, w: Work, +job: T.Appraisal, +c: Cand) -> Work:
  match w:
    case Work{+t, b, e}:
      Work.done(Forest.put(t, Cand.slot(c), cap, job, Cand.at(c)), b, e)

def Work.exception(w: Work, x: T.Exception) -> Work:
  match w:
    case Work{t, b, e}:
      Work{t, b, x <> e}

def Work.wait(w: Work, job: T.Appraisal) -> Work:
  match w:
    case Work{t, b, e}:
      Work{t, job <> b, e}

def hold(w: Work, +job: T.Appraisal, urgent: Bool, reason: T.Reason) -> Work:
  match urgent:
    case True{}:
      Work.exception(w, T.Exception{job, reason})
    case False{}:
      Work.wait(w, job)

def place.outside(m: Maybe<&2, Cand>, +cap: Nat, +w: Work, +job: T.Appraisal) -> Work:
  match m:
    case Some{c}:
      place.apply(cap, w, job, c)
    case None{}:
      hold(w, job, True{}, T.NoCapacity{})

# Crossing a zip boundary is only allowed to save a deadline.
def place.rescue(c: Bool, +d: Nat, +cap: Nat, +w: Work, +job: T.Appraisal) -> Work:
  match c:
    case True{}:
      place.outside(Select.tree(Work.tree(w), d, cap, job, True{}), cap, w, job)
    case False{}:
      hold(w, job, False{}, T.NoCapacity{})

def place(m: Maybe<&2, Cand>, +d: Nat, +cap: Nat, +last: Nat, +w: Work, +job: T.Appraisal) -> Work:
  match m:
    case Some{c}:
      place.apply(cap, w, job, c)
    case None{}:
      place.rescue(Nat.is_lt(T.Appraisal.due(job), last), d, cap, w, job)

# Tightest deadline first, each to its cheapest open spot.
def assign(jobs: List<&2, T.Appraisal>, +d: Nat, +cap: Nat, +last: Nat, +w: Work) -> Work:
  match jobs:
    case Nil{}:
      w
    case +j <> t:
      assign(t, d, cap, last, place(Select.tree(Work.tree(w), d, cap, j, False{}), d, cap, last, w, j))

def Work.plan(w: Work) -> T.Plan:
  match w:
    case Work{t, b, e}:
      T.Plan{Forest.routes(t), b, e}

# Improving routes
# ----------------

def loop_cost(+crew: T.Contractor, +h: List<&2, T.Stop>, +t: List<&2, T.Stop>) -> Nat:
  R.Route.loop_drive(crew, R.Stops.append(h, t))

# t with positions i up to j reversed.
def flip(+t: List<&2, T.Stop>, +i: Nat, +j: Nat) -> List<&2, T.Stop>:
  +front = List.take(&2, T.Stop, t, i)
  +mid = List.take(&2, T.Stop, List.drop(&2, T.Stop, t, i), Nat.sub(j, i))
  +back = List.drop(&2, T.Stop, t, j)
  R.Stops.append(front, R.Stops.append(List.reverse(&2, T.Stop, mid), back))

type Try is Data:
  Try{tail: List<&2, T.Stop>, cost: Nat}

def Try.tail(t: Try) -> List<&2, T.Stop>:
  match t:
    case Try{a, b}:
      a

def Try.cost(t: Try) -> Nat:
  match t:
    case Try{a, b}:
      b

def Try.pick(c: Bool, x: Try, y: Try) -> Try:
  match c:
    case True{}:
      y
    case False{}:
      x

def Try.flip(+crew: T.Contractor, +h: List<&2, T.Stop>, +t: List<&2, T.Stop>, +i: Nat, +j: Nat, +best: Try) -> Try:
  +next = flip(t, i, j)
  +cost = loop_cost(crew, h, next)
  Try.pick(Nat.is_lt(cost, Try.cost(best)), best, Try{next, cost})

def scan.j(fuel: Nat, +crew: T.Contractor, +h: List<&2, T.Stop>, +t: List<&2, T.Stop>, +i: Nat, +j: Nat, +best: Try) -> Try:
  match fuel:
    case 0n:
      best
    case 1n+f:
      scan.j(f, crew, h, t, i, 1n+j, Try.flip(crew, h, t, i, j, best))

def scan.i(fuel: Nat, +crew: T.Contractor, +h: List<&2, T.Stop>, +t: List<&2, T.Stop>, +i: Nat, +size: Nat, +best: Try) -> Try:
  match fuel:
    case 0n:
      best
    case 1n+f:
      scan.i(f, crew, h, t, 1n+i, size, scan.j(Nat.sub(size, Nat.add(i, 1n)), crew, h, t, i, Nat.add(i, 2n), best))

# One round of 2-opt: the best segment reversal, if any shortens the loop.
def two_opt.step(+crew: T.Contractor, +h: List<&2, T.Stop>, +t: List<&2, T.Stop>) -> Try:
  +size = List.length(&2, T.Stop, t)
  scan.i(size, crew, h, t, 0n, size, Try{t, loop_cost(crew, h, t)})

def two_opt.if(c: Bool, +t: List<&2, T.Stop>, next: Unit -> List<&2, T.Stop>) -> List<&2, T.Stop>:
  match c:
    case True{}:
      next(Unit{})
    case False{}:
      t

def two_opt(fuel: Nat, +crew: T.Contractor, +h: List<&2, T.Stop>, +t: List<&2, T.Stop>) -> List<&2, T.Stop>:
  match fuel:
    case 0n:
      t
    case 1n+f:
      +step = two_opt.step(crew, h, t)
      two_opt.if(Nat.is_lt(Try.cost(step), loop_cost(crew, h, t)), t, u => two_opt(f, crew, h, Try.tail(step)))

# Reorders through the same edit healing uses, so a bad reversal can't lose a stop.
def Route.polish(+cap: Nat, +r: T.Route) -> R.Step:
  +crew = T.Route.crew(r)
  +t = two_opt(6n, crew, H.Route.h(r), H.Route.t(r))
  H.Route.apply(cap, H.Reorder{T.Contractor.id(crew), T.Route.day(r), t}, r)

def Route.work(+r: T.Route) -> Nat:
  +k = List.length(&2, T.Stop, T.Route.stops(r))
  Nat.add(1n, Nat.mul(k, Nat.mul(k, k)))

def Routes.work(routes: List<&2, T.Route>) -> Nat:
  match routes:
    case Nil{}:
      0n
    case +r <> t:
      Nat.add(Route.work(r), Routes.work(t))

def split_at.if(c: Bool, +half: Nat, +at: Nat, +w: Nat, next: Unit -> Nat) -> Nat:
  match c:
    case True{}:
      Nat.max(at, 1n)
    case False{}:
      next(Unit{})

# How many routes from the front hold half the work. 2-opt cost grows with the
# cube of a route's stops, so splitting by count would leave lanes idle.
def split_at(routes: List<&2, T.Route>, +half: Nat, +at: Nat) -> Nat:
  match routes:
    case Nil{}:
      at
    case +r <> t:
      split_at.if(Nat.is_ge(Route.work(r), half), half, at, Route.work(r), u => split_at(t, Nat.sub(half, Route.work(r)), 1n+at))

def Edited.join(a: H.Edited, b: H.Edited) -> H.Edited:
  match a b:
    case H.Edited{r1, s1} H.Edited{r2, s2}:
      H.Edited{List.append(&2, T.Route, r1, r2), R.Stops.append(s1, s2)}

def polish.seq(routes: List<&2, T.Route>, +cap: Nat) -> H.Edited:
  match routes:
    case Nil{}:
      H.Edited{Nil{}, Nil{}}
    case r <> t:
      H.Edited.cons(Route.polish(cap, r), polish.seq(t, cap))

# Routes are independent, so this is where the planner gets its speedup.
def polish.par(+fuel: Nat, +routes: List<&2, T.Route>, +cap: Nat) -> H.Edited:
  match fuel:
    case 0n:
      polish.seq(routes, cap)
    case 1n+f:
      +at = split_at(routes, Nat.div(Routes.work(routes), 2n), 0n)
      a b = polish.par(f, List.take(&2, T.Route, routes, at), cap) polish.par(f, List.drop(&2, T.Route, routes, at), cap)
      Edited.join(a, b)

# Scoring
# -------

type Tally is Data:
  Tally{late: Nat, peak: Nat, total: Nat}

def Tally.add(+r: T.Route, t: Tally) -> Tally:
  match t:
    case Tally{+l, +p, +s}:
      +a = T.Route.audit(r)
      Tally{Nat.add(l, List.length(&2, Nat, T.Audit.late(a))), Nat.max(p, T.Audit.minutes(a)), Nat.add(s, T.Audit.minutes(a))}

def Routes.tally(routes: List<&2, T.Route>) -> Tally:
  match routes:
    case Nil{}:
      Tally{0n, 0n, 0n}
    case +r <> t:
      Tally.add(r, Routes.tally(t))

# Lower is better, in priority order: work left unplaced, deadlines missed, the
# longest day, then total minutes.
def score.go(+unplaced: Nat, t: Tally) -> Nat:
  match t:
    case Tally{l, p, s}:
      Nat.add(Nat.mul(Nat.mul(unplaced, 100000n), 1000000n), Nat.add(Nat.mul(l, 1000000000n), Nat.add(Nat.mul(p, 100000n), s)))

def score(+plan: T.Plan) -> Nat:
  +unplaced = Nat.add(List.length(&2, T.Appraisal, T.Plan.backlog(plan)), List.length(&2, T.Exception, T.Plan.exceptions(plan)))
  score.go(unplaced, Routes.tally(T.Plan.routes(plan)))

# One pass of polishing every route.
def pass(+cap: Nat, +plan: T.Plan) -> T.Plan:
  +done = polish.par(4n, T.Plan.routes(plan), cap)
  H.Plan.with(H.Edited.routes(done), H.Edited.shed(done), T.Plan.backlog(plan), T.Plan.exceptions(plan))

def keep_better(c: Bool, plan: T.Plan, next: T.Plan) -> T.Plan:
  match c:
    case True{}:
      next
    case False{}:
      plan

def accepts(+inst: T.Instance, +plan: T.Plan, +next: T.Plan) -> Bool:
  Bool.and(Nat.is_lt(score(next), score(plan)), P.Plan.check(inst, next))

# Takes a step only if it scores better and passes the checker, so the score
# never gets worse and a valid plan stays valid.
def improve(fuel: Nat, +inst: T.Instance, +plan: T.Plan) -> T.Plan:
  match fuel:
    case 0n:
      plan
    case 1n+f:
      +next = pass(T.Instance.cap(inst), plan)
      improve(f, inst, keep_better(accepts(inst, plan, next), plan, next))

def publish.if(c: Bool, +inst: T.Instance, plan: T.Plan) -> T.Plan:
  match c:
    case True{}:
      plan
    case False{}:
      P.Plan.trivial(inst)

# The only way out of the planner. A plan that fails the proven checker never
# leaves, however it was made.
def publish(+inst: T.Instance, +plan: T.Plan) -> T.Plan:
  publish.if(P.Plan.check(inst, plan), inst, plan)

# Planner settings. These are parameters rather than constants because a literal
# fuel inside solve would make the proof checker unroll it when comparing terms.
type Tuning is Data:
  Tuning{passes: Nat, lanes: Nat, depth: Nat}

def Tuning.passes(t: Tuning) -> Nat:
  match t:
    case Tuning{p, l, d}:
      p

def Tuning.lanes(t: Tuning) -> Nat:
  match t:
    case Tuning{p, l, d}:
      l

def Tuning.depth(t: Tuning) -> Nat:
  match t:
    case Tuning{p, l, d}:
      d

# Three passes of polish. lanes forks the search 2^6 ways, far more than there are
# cores: a job's candidates cluster on a few routes and a task never moves once
# assigned, so small tasks are what balance the load. Measured, not guessed: 2^2
# gave 1.3x and 2^6 gave 2.9x on 4,000 jobs. depth is only a termination bound on
# building the tree, and 2^32 routes is more than any plan holds.
def Tuning.standard() -> Tuning:
  Tuning{3n, 6n, 32n}

# first is the first day planned and last the day after the end of the horizon.
def plan(+tune: Tuning, +inst: T.Instance, +first: Nat, +last: Nat) -> T.Plan:
  +routes = blank(T.Instance.crews(inst), first, last)
  +tree = Forest.of(Tuning.depth(tune), List.length(&2, T.Route, routes), routes)
  +jobs = List.sort(~T.Appraisal, ~by_due, T.Instance.jobs(inst))
  Work.plan(assign(jobs, Tuning.lanes(tune), T.Instance.cap(inst), last, Work{tree, Nil{}, Nil{}}))

def solve(+tune: Tuning, +inst: T.Instance, +first: Nat, +last: Nat) -> T.Plan:
  publish(inst, improve(Tuning.passes(tune), inst, plan(tune, inst, first, last)))
