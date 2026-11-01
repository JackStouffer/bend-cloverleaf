import Base

# Domain types for the pure core. Everything numeric is a Nat: it runs as a
# 48-bit immediate as fast as a U32, traps on overflow instead of wrapping, and
# induction on it needs no bit-level lemmas.

# Coordinates are degrees times 10000. Longitude counts degrees west, because
# the lower 48 are all west of Greenwich and Nat has no negatives.
type Point is Data:
  Point{lat: Nat, lon: Nat}

type Status is Data:
  Open{}
  Underway{}
  Completed{}
  Failed{}
  Cancelled{}

# An appraisal request. Immutable once created: where it is and how far along
# it is live in the plan, so the request itself never has two copies to update.
type Appraisal is Data:
  Appraisal{id: Nat, site: Point, zip: Nat, due: Nat, minutes: Nat, state: Nat}

type Contractor is Data:
  Contractor{id: Nat, home: Point, zips: List<&2, Nat>, max_minutes: Nat, days: List<&2, Nat>, state: Nat}

type Stop is Data:
  Stop{job: Appraisal, status: Status}

# What a route costs and where it breaks a soft rule. Published with the route,
# and the checker rejects a plan whose audit isn't the truth.
type Audit is Data:
  Audit{minutes: Nat, extra: Nat, overtime: Bool, off_day: Bool, late: List<&2, Nat>, outside: List<&2, Nat>}

# A route is a loop from the crew's home. `closed` stops new work landing on it,
# for example when the contractor goes home sick.
type Route is Data:
  Route{crew: Contractor, day: Nat, stops: List<&2, Stop>, closed: Bool, audit: Audit}

type Reason is Data:
  NoCapacity{}

type Exception is Data:
  Exception{job: Appraisal, reason: Reason}

type Plan is Data:
  Plan{routes: List<&2, Route>, backlog: List<&2, Appraisal>, exceptions: List<&2, Exception>}

# One instance is one state: contractors never work across a state line, so the
# national solve is one independent instance per state. crews and jobs are kept
# sorted by id, with each id once. cap is the out-of-zip drive-time limit in minutes.
type Instance is Data:
  Instance{crews: List<&2, Contractor>, jobs: List<&2, Appraisal>, cap: Nat, state: Nat}

# Accessors
# ---------

def Point.lat(p: Point) -> Nat:
  match p:
    case Point{a, b}:
      a

def Point.lon(p: Point) -> Nat:
  match p:
    case Point{a, b}:
      b

def Appraisal.id(a: Appraisal) -> Nat:
  match a:
    case Appraisal{i, s, z, d, m, t}:
      i

def Appraisal.site(a: Appraisal) -> Point:
  match a:
    case Appraisal{i, s, z, d, m, t}:
      s

def Appraisal.zip(a: Appraisal) -> Nat:
  match a:
    case Appraisal{i, s, z, d, m, t}:
      z

def Appraisal.due(a: Appraisal) -> Nat:
  match a:
    case Appraisal{i, s, z, d, m, t}:
      d

def Appraisal.minutes(a: Appraisal) -> Nat:
  match a:
    case Appraisal{i, s, z, d, m, t}:
      m

def Contractor.id(c: Contractor) -> Nat:
  match c:
    case Contractor{i, h, z, m, d, t}:
      i

def Contractor.home(c: Contractor) -> Point:
  match c:
    case Contractor{i, h, z, m, d, t}:
      h

def Contractor.zips(c: Contractor) -> List<&2, Nat>:
  match c:
    case Contractor{i, h, z, m, d, t}:
      z

def Contractor.max_minutes(c: Contractor) -> Nat:
  match c:
    case Contractor{i, h, z, m, d, t}:
      m

def Contractor.days(c: Contractor) -> List<&2, Nat>:
  match c:
    case Contractor{i, h, z, m, d, t}:
      d

def Appraisal.state(a: Appraisal) -> Nat:
  match a:
    case Appraisal{i, s, z, d, m, t}:
      t

def Contractor.state(c: Contractor) -> Nat:
  match c:
    case Contractor{i, h, z, m, d, t}:
      t

def Stop.job(s: Stop) -> Appraisal:
  match s:
    case Stop{j, t}:
      j

def Stop.status(s: Stop) -> Status:
  match s:
    case Stop{j, t}:
      t

def Stop.id(s: Stop) -> Nat:
  Appraisal.id(Stop.job(s))

def Audit.minutes(a: Audit) -> Nat:
  match a:
    case Audit{m, e, o, f, l, u}:
      m

def Audit.extra(a: Audit) -> Nat:
  match a:
    case Audit{m, e, o, f, l, u}:
      e

def Audit.overtime(a: Audit) -> Bool:
  match a:
    case Audit{m, e, o, f, l, u}:
      o

def Audit.off_day(a: Audit) -> Bool:
  match a:
    case Audit{m, e, o, f, l, u}:
      f

def Audit.late(a: Audit) -> List<&2, Nat>:
  match a:
    case Audit{m, e, o, f, l, u}:
      l

def Audit.outside(a: Audit) -> List<&2, Nat>:
  match a:
    case Audit{m, e, o, f, l, u}:
      u

def Route.crew(r: Route) -> Contractor:
  match r:
    case Route{c, d, s, k, a}:
      c

def Route.day(r: Route) -> Nat:
  match r:
    case Route{c, d, s, k, a}:
      d

def Route.stops(r: Route) -> List<&2, Stop>:
  match r:
    case Route{c, d, s, k, a}:
      s

def Route.closed(r: Route) -> Bool:
  match r:
    case Route{c, d, s, k, a}:
      k

def Route.audit(r: Route) -> Audit:
  match r:
    case Route{c, d, s, k, a}:
      a

def Exception.job(e: Exception) -> Appraisal:
  match e:
    case Exception{j, r}:
      j

def Plan.routes(p: Plan) -> List<&2, Route>:
  match p:
    case Plan{r, b, e}:
      r

def Plan.backlog(p: Plan) -> List<&2, Appraisal>:
  match p:
    case Plan{r, b, e}:
      b

def Plan.exceptions(p: Plan) -> List<&2, Exception>:
  match p:
    case Plan{r, b, e}:
      e

def Instance.state(i: Instance) -> Nat:
  match i:
    case Instance{c, j, k, s}:
      s

def Instance.crews(i: Instance) -> List<&2, Contractor>:
  match i:
    case Instance{c, j, k, s}:
      c

def Instance.jobs(i: Instance) -> List<&2, Appraisal>:
  match i:
    case Instance{c, j, k, s}:
      j

def Instance.cap(i: Instance) -> Nat:
  match i:
    case Instance{c, j, k, s}:
      k

# Equality
# --------

def Nats.is_eq(xs: List<&2, Nat>, ys: List<&2, Nat>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Nil{} y <> yt:
      False{}
    case x <> xt Nil{}:
      False{}
    case x <> xt y <> yt:
      Bool.and(Nat.is_eq(x, y), Nats.is_eq(xt, yt))

def Bool.is_eq(a: Bool, b: Bool) -> Bool:
  match a:
    case True{}:
      b
    case False{}:
      Bool.not(b)

def Point.is_eq(a: Point, b: Point) -> Bool:
  match a b:
    case Point{x1, y1} Point{x2, y2}:
      Bool.and(Nat.is_eq(x1, x2), Nat.is_eq(y1, y2))

def Appraisal.is_eq(a: Appraisal, b: Appraisal) -> Bool:
  match a b:
    case Appraisal{i1, s1, z1, d1, m1, t1} Appraisal{i2, s2, z2, d2, m2, t2}:
      Bool.and(Nat.is_eq(i1, i2), Bool.and(Point.is_eq(s1, s2),
        Bool.and(Nat.is_eq(z1, z2), Bool.and(Nat.is_eq(d1, d2), Bool.and(Nat.is_eq(m1, m2), Nat.is_eq(t1, t2))))))

def Contractor.is_eq(a: Contractor, b: Contractor) -> Bool:
  match a b:
    case Contractor{i1, h1, z1, m1, d1, t1} Contractor{i2, h2, z2, m2, d2, t2}:
      Bool.and(Nat.is_eq(i1, i2), Bool.and(Point.is_eq(h1, h2),
        Bool.and(Nats.is_eq(z1, z2), Bool.and(Nat.is_eq(m1, m2), Bool.and(Nats.is_eq(d1, d2), Nat.is_eq(t1, t2))))))

def Audit.is_eq(a: Audit, b: Audit) -> Bool:
  match a b:
    case Audit{m1, e1, o1, f1, l1, u1} Audit{m2, e2, o2, f2, l2, u2}:
      Bool.and(Nat.is_eq(m1, m2), Bool.and(Nat.is_eq(e1, e2),
        Bool.and(Bool.is_eq(o1, o2), Bool.and(Bool.is_eq(f1, f2),
          Bool.and(Nats.is_eq(l1, l2), Nats.is_eq(u1, u2))))))
