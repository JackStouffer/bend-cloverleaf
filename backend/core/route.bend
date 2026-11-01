import Base
import ./types.bend as T
import ./lifecycle.bend as Life
import ./geo.bend as Geo

# One contractor's day. A route is a locked head (stops underway or done, in the
# order worked) then an open tail the planner may rearrange.

type Test is Data:
  HasId{id: Nat}
  IsUnderway{id: Nat}
  InZips{zips: List<&2, Nat>}

def Nats.has(xs: List<&2, Nat>, +x: Nat) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case h <> t:
      Bool.or(Nat.is_eq(h, x), Nats.has(t, x))

def Stop.locked(s: T.Stop) -> Bool:
  Life.Status.locked(T.Stop.status(s))

def Stop.open(s: T.Stop) -> Bool:
  Life.Status.is_open(T.Stop.status(s))

def Stop.zip(s: T.Stop) -> Nat:
  T.Appraisal.zip(T.Stop.job(s))

def Stop.site(s: T.Stop) -> T.Point:
  T.Appraisal.site(T.Stop.job(s))

def Test.run(t: Test, +s: T.Stop) -> Bool:
  match t:
    case HasId{i}:
      Nat.is_eq(T.Stop.id(s), i)
    case IsUnderway{i}:
      Bool.and(Nat.is_eq(T.Stop.id(s), i), Life.Status.is_underway(T.Stop.status(s)))
    case InZips{z}:
      Nats.has(z, Stop.zip(s))

def Stops.put(c: Bool, s: T.Stop, r: List<&2, T.Stop>) -> List<&2, T.Stop>:
  match c:
    case True{}:
      s <> r
    case False{}:
      r

def Stops.keep(stops: List<&2, T.Stop>, +t: Test) -> List<&2, T.Stop>:
  match stops:
    case Nil{}:
      Nil{}
    case +s <> r:
      Stops.put(Test.run(t, s), s, Stops.keep(r, t))

def Stops.cut(stops: List<&2, T.Stop>, +t: Test) -> List<&2, T.Stop>:
  match stops:
    case Nil{}:
      Nil{}
    case +s <> r:
      Stops.put(Bool.not(Test.run(t, s)), s, Stops.cut(r, t))

def Stops.any(stops: List<&2, T.Stop>, +t: Test) -> Bool:
  match stops:
    case Nil{}:
      False{}
    case +s <> r:
      Bool.or(Test.run(t, s), Stops.any(r, t))

def Stops.head.put(c: Bool, s: T.Stop, r: List<&2, T.Stop>) -> List<&2, T.Stop>:
  match c:
    case True{}:
      s <> r
    case False{}:
      Nil{}

# The locked stops in front.
def Stops.head(stops: List<&2, T.Stop>) -> List<&2, T.Stop>:
  match stops:
    case Nil{}:
      Nil{}
    case +s <> r:
      Stops.head.put(Stop.locked(s), s, Stops.head(r))

def Stops.tail.put(c: Bool, s: T.Stop, r: List<&2, T.Stop>, rest: List<&2, T.Stop>) -> List<&2, T.Stop>:
  match c:
    case True{}:
      rest
    case False{}:
      s <> r

# Everything from the first unlocked stop on.
def Stops.tail(stops: List<&2, T.Stop>) -> List<&2, T.Stop>:
  match stops:
    case Nil{}:
      Nil{}
    case +s <> +r:
      Stops.tail.put(Stop.locked(s), s, r, Stops.tail(r))

def Stops.all_locked(stops: List<&2, T.Stop>) -> Bool:
  match stops:
    case Nil{}:
      True{}
    case +s <> r:
      Bool.and(Stop.locked(s), Stops.all_locked(r))

def Stops.all_open(stops: List<&2, T.Stop>) -> Bool:
  match stops:
    case Nil{}:
      True{}
    case +s <> r:
      Bool.and(Stop.open(s), Stops.all_open(r))

# Every locked stop in visit order, which healing must leave alone.
def Stops.locked(stops: List<&2, T.Stop>) -> List<&2, T.Stop>:
  match stops:
    case Nil{}:
      Nil{}
    case +s <> r:
      Stops.put(Stop.locked(s), s, Stops.locked(r))

def Stops.append(xs: List<&2, T.Stop>, ys: List<&2, T.Stop>) -> List<&2, T.Stop>:
  List.append(&2, T.Stop, xs, ys)

def Stops.jobs(stops: List<&2, T.Stop>) -> List<&2, T.Appraisal>:
  match stops:
    case Nil{}:
      Nil{}
    case s <> r:
      T.Stop.job(s) <> Stops.jobs(r)

# Drive minutes from `from` through the stops and back to home.
def Stops.drive(stops: List<&2, T.Stop>, +from: T.Point, +home: T.Point) -> Nat:
  match stops:
    case Nil{}:
      Geo.minutes(from, home)
    case s <> r:
      +site = Stop.site(s)
      Nat.add(Geo.minutes(from, site), Stops.drive(r, site, home))

def Stops.service(stops: List<&2, T.Stop>) -> Nat:
  match stops:
    case Nil{}:
      0n
    case s <> r:
      Nat.add(T.Appraisal.minutes(T.Stop.job(s)), Stops.service(r))

def Stops.late.put(c: Bool, i: Nat, r: List<&2, Nat>) -> List<&2, Nat>:
  match c:
    case True{}:
      i <> r
    case False{}:
      r

def Stops.late(stops: List<&2, T.Stop>, +day: Nat) -> List<&2, Nat>:
  match stops:
    case Nil{}:
      Nil{}
    case +s <> r:
      Stops.late.put(Nat.is_gt(day, T.Appraisal.due(T.Stop.job(s))), T.Stop.id(s), Stops.late(r, day))

def Stops.outside(stops: List<&2, T.Stop>, +zips: List<&2, Nat>) -> List<&2, Nat>:
  match stops:
    case Nil{}:
      Nil{}
    case +s <> r:
      Stops.late.put(Bool.not(Nats.has(zips, Stop.zip(s))), T.Stop.id(s), Stops.outside(r, zips))

def Crew.inside(c: T.Contractor) -> Test:
  InZips{T.Contractor.zips(c)}

def Route.loop_drive(+crew: T.Contractor, stops: List<&2, T.Stop>) -> Nat:
  +home = T.Contractor.home(crew)
  Stops.drive(stops, home, home)

# Drive time owed to unlocked out-of-zip stops. Locked ones are sunk, so healing
# can always bring a route back under the cap by shedding what's left.
def Route.extra(+crew: T.Contractor, +stops: List<&2, T.Stop>) -> Nat:
  +inside = Stops.keep(Stops.tail(stops), Crew.inside(crew))
  Nat.sub(Route.loop_drive(crew, stops), Route.loop_drive(crew, Stops.append(Stops.head(stops), inside)))

# Drive time plus time on site.
def Route.worked(+crew: T.Contractor, +stops: List<&2, T.Stop>) -> Nat:
  Nat.add(Route.loop_drive(crew, stops), Stops.service(stops))

def Audit.of(+crew: T.Contractor, +day: Nat, +stops: List<&2, T.Stop>) -> T.Audit:
  +minutes = Route.worked(crew, stops)
  T.Audit{minutes, Route.extra(crew, stops), Nat.is_gt(minutes, T.Contractor.max_minutes(crew)),
    Bool.not(Nats.has(T.Contractor.days(crew), day)), Stops.late(stops, day),
    Stops.outside(stops, T.Contractor.zips(crew))}

def Route.seal(+crew: T.Contractor, +day: Nat, +stops: List<&2, T.Stop>, closed: Bool) -> T.Route:
  T.Route{crew, day, stops, closed, Audit.of(crew, day, stops)}

type Step is Data:
  Step{route: T.Route, shed: List<&2, T.Stop>}

def Step.route(s: Step) -> T.Route:
  match s:
    case Step{r, x}:
      r

def Step.shed(s: Step) -> List<&2, T.Stop>:
  match s:
    case Step{r, x}:
      x

def Step.add(out: List<&2, T.Stop>, s: Step) -> Step:
  match s:
    case Step{r, x}:
      Step{r, Stops.append(out, x)}

def Route.remake.if(c: Bool, +crew: T.Contractor, +day: Nat, closed: Bool, +h: List<&2, T.Stop>, +t: List<&2, T.Stop>) -> Step:
  match c:
    case True{}:
      Step{Route.seal(crew, day, Stops.append(h, t), closed), Nil{}}
    case False{}:
      Step{Route.seal(crew, day, Stops.append(h, Stops.keep(t, Crew.inside(crew))), closed),
        Stops.cut(t, Crew.inside(crew))}

# Rebuilds a route from a head and a tail, shedding unlocked out-of-zip stops if
# they cost more than the cap. Every route that leaves here is valid.
def Route.remake(+cap: Nat, +crew: T.Contractor, +day: Nat, closed: Bool, +h: List<&2, T.Stop>, +t: List<&2, T.Stop>) -> Step:
  Route.remake.if(Nat.is_le(Route.extra(crew, Stops.append(h, t)), cap), crew, day, closed, h, t)

def Route.ok(+cap: Nat, r: T.Route) -> Bool:
  match r:
    case T.Route{c, d, +s, k, +a}:
      Bool.and(Stops.all_open(Stops.tail(s)),
        Bool.and(T.Audit.is_eq(a, Audit.of(c, d, s)), Nat.is_le(T.Audit.extra(a), cap)))

def Route.path.go(stops: List<&2, T.Stop>, +home: T.Point) -> List<&2, T.Point>:
  match stops:
    case Nil{}:
      [home]
    case s <> r:
      Stop.site(s) <> Route.path.go(r, home)

# The closed loop a route drives, for maps and for the loop law.
def Route.path(+r: T.Route) -> List<&2, T.Point>:
  +home = T.Contractor.home(T.Route.crew(r))
  home <> Route.path.go(T.Route.stops(r), home)
