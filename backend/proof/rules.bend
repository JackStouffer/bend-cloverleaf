import Base
import ../core/types.bend as T
import ../core/jobs.bend as J
import ../core/route.bend as R
import ../core/plan.bend as P
import ../core/heal.bend as H
import ./logic.bend as L
import ./jobs.bend as PJ
import ./route.bend as PR
import ./heal.bend as PH
import ./plan.bend as PP

# What a passing checker promises, route by route. Everything here takes a route
# from a valid plan by its index, so it applies to every route.

def ST() -> Data:
  List<&2, T.Stop>

def RL() -> Data:
  List<&2, T.Route>

def JC(+a: T.Appraisal, xs: ST()) -> Nat:
  J.count(a, R.Stops.jobs(xs))

def Crews() -> Data:
  List<&2, T.Contractor>

def At(+routes: RL(), +n: Nat, +r: T.Route) -> Data:
  {List.get(&2, T.Route, routes, n) == Some{r} : Maybe<&2, T.Route>}

def Unsome(m: Maybe<&2, T.Route>, +d: T.Route) -> T.Route:
  Maybe.default(&2, T.Route, m, d)

law some_route:
  for +a: T.Route
  for +b: T.Route
  for +e: {Some{a} == Some{b} : Maybe<&2, T.Route>}
  {a == b : T.Route}

def some_route(a, b, e):
  Equal.cong(Maybe<&2, T.Route>, T.Route, m => Unsome(m, a), Some{a}, Some{b}, e)

law none_is_not_some:
  for +a: T.Route
  for +e: {None{} == Some{a} : Maybe<&2, T.Route>}
  Empty

def NoneDisc(m: Maybe<&2, T.Route>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      Empty

def none_is_not_some(a, e):
  %e : NoneDisc(_)
  Unit{}

# Every route in a passing list is fine.
law fine_at:
  for +routes: RL()
  for +crews: Crews()
  for +cap: Nat
  for +n: Nat
  for +r: T.Route
  for +er: {P.Routes.ok(routes, crews, cap) == True{} : Bool}
  for +at: At(routes, n, r)
  {P.Route.fine(crews, cap, r) == True{} : Bool}

def fine_at(routes, crews, cap, n, r, er, at):
  match routes n:
    case Nil{} _:
      Empty.absurd({P.Route.fine(crews, cap, r) == True{} : Bool}, none_is_not_some(r, at))
    case +h <> +t 0n:
      %some_route(h, r, at) : {P.Route.fine(crews, cap, _) == True{} : Bool}
      PP.routes_head(h, t, crews, cap, er)
    case +h <> +t 1n+p:
      fine_at(t, crews, cap, p, r, PP.routes_tail(h, t, crews, cap, er), at)

law fine_valid:
  for +inst: T.Instance
  for +plan: T.Plan
  for +n: Nat
  for +r: T.Route
  for +ev: {P.Plan.valid(inst, plan) == True{} : Bool}
  for +at: At(T.Plan.routes(plan), n, r)
  {P.Route.fine(T.Instance.crews(inst), T.Instance.cap(inst), r) == True{} : Bool}

def fine_valid(inst, plan, n, r, ev, at):
  fine_at(T.Plan.routes(plan), T.Instance.crews(inst), T.Instance.cap(inst), n, r, PP.v_routes(inst, plan, ev), at)

law ok_valid:
  for +inst: T.Instance
  for +plan: T.Plan
  for +n: Nat
  for +r: T.Route
  for +ev: {P.Plan.valid(inst, plan) == True{} : Bool}
  for +at: At(T.Plan.routes(plan), n, r)
  {R.Route.ok(T.Instance.cap(inst), r) == True{} : Bool}

def ok_valid(inst, plan, n, r, ev, at):
  PP.ok_of_fine(T.Instance.crews(inst), T.Instance.cap(inst), r, fine_valid(inst, plan, n, r, ev, at))

# Audits
# ------

law audit_of:
  for +a: T.Audit
  for +b: T.Audit
  for +e: {T.Audit.is_eq(a, b) == True{} : Bool}
  {a == b : T.Audit}

law audit_of.go:
  for +m1: Nat
  for +m2: Nat
  for +e1: Nat
  for +e2: Nat
  for +o1: Bool
  for +o2: Bool
  for +f1: Bool
  for +f2: Bool
  for +l1: List<&2, Nat>
  for +l2: List<&2, Nat>
  for +u1: List<&2, Nat>
  for +u2: List<&2, Nat>
  for +em: {m1 == m2 : Nat}
  for +ee: {e1 == e2 : Nat}
  for +eo: {o1 == o2 : Bool}
  for +ef: {f1 == f2 : Bool}
  for +el: {l1 == l2 : List<&2, Nat>}
  for +eu: {u1 == u2 : List<&2, Nat>}
  {T.Audit{m1, e1, o1, f1, l1, u1} == T.Audit{m2, e2, o2, f2, l2, u2} : T.Audit}

def audit_of.go(m1, m2, e1, e2, o1, o2, f1, f2, l1, l2, u1, u2, em, ee, eo, ef, el, eu):
  %em : {T.Audit{m1, e1, o1, f1, l1, u1} == T.Audit{_, e2, o2, f2, l2, u2} : T.Audit}
  %ee : {T.Audit{m1, e1, o1, f1, l1, u1} == T.Audit{m1, _, o2, f2, l2, u2} : T.Audit}
  %eo : {T.Audit{m1, e1, o1, f1, l1, u1} == T.Audit{m1, e1, _, f2, l2, u2} : T.Audit}
  %ef : {T.Audit{m1, e1, o1, f1, l1, u1} == T.Audit{m1, e1, o1, _, l2, u2} : T.Audit}
  %el : {T.Audit{m1, e1, o1, f1, l1, u1} == T.Audit{m1, e1, o1, f1, _, u2} : T.Audit}
  %eu : {T.Audit{m1, e1, o1, f1, l1, u1} == T.Audit{m1, e1, o1, f1, l1, _} : T.Audit}
  {==}

def audit_of(a, b, e):
  match a b:
    case T.Audit{m1, e1, o1, f1, l1, u1} T.Audit{m2, e2, o2, f2, l2, u2}:
      +r4 = Bool.and(T.Nats.is_eq(l1, l2), T.Nats.is_eq(u1, u2))
      +r3 = Bool.and(T.Bool.is_eq(f1, f2), r4)
      +r2 = Bool.and(T.Bool.is_eq(o1, o2), r3)
      +r1 = Bool.and(Nat.is_eq(e1, e2), r2)
      +s1 = L.and_r(Nat.is_eq(m1, m2), r1, e)
      +s2 = L.and_r(Nat.is_eq(e1, e2), r2, s1)
      +s3 = L.and_r(T.Bool.is_eq(o1, o2), r3, s2)
      +s4 = L.and_r(T.Bool.is_eq(f1, f2), r4, s3)
      audit_of.go(m1, m2, e1, e2, o1, o2, f1, f2, l1, l2, u1, u2,
        L.eq_of(m1, m2, L.and_l(Nat.is_eq(m1, m2), r1, e)),
        L.eq_of(e1, e2, L.and_l(Nat.is_eq(e1, e2), r2, s1)),
        L.bool_of(o1, o2, L.and_l(T.Bool.is_eq(o1, o2), r3, s2)),
        L.bool_of(f1, f2, L.and_l(T.Bool.is_eq(f1, f2), r4, s3)),
        L.nats_of(l1, l2, L.and_l(T.Nats.is_eq(l1, l2), T.Nats.is_eq(u1, u2), s4)),
        L.nats_of(u1, u2, L.and_r(T.Nats.is_eq(l1, l2), T.Nats.is_eq(u1, u2), s4)))

def Truth(+r: T.Route) -> T.Audit:
  R.Audit.of(T.Route.crew(r), T.Route.day(r), T.Route.stops(r))

# A route that passes publishes the true audit.
law audit_true:
  for +cap: Nat
  for +r: T.Route
  for +e: {R.Route.ok(cap, r) == True{} : Bool}
  {T.Route.audit(r) == Truth(r) : T.Audit}

def audit_true(cap, r, e):
  match r:
    case T.Route{c, d, s, k, a}:
      +t = R.Audit.of(c, d, s)
      audit_of(a, t, L.and_l(T.Audit.is_eq(a, t), Nat.is_le(T.Audit.extra(a), cap),
        L.and_r(R.Stops.all_open(R.Stops.tail(s)), Bool.and(T.Audit.is_eq(a, t), Nat.is_le(T.Audit.extra(a), cap)), e)))

law extra_true:
  for +cap: Nat
  for +r: T.Route
  for +e: {R.Route.ok(cap, r) == True{} : Bool}
  {Nat.is_le(R.Route.extra(T.Route.crew(r), T.Route.stops(r)), cap) == True{} : Bool}

def extra_true(cap, r, e):
  match r:
    case T.Route{c, d, s, k, a}:
      +t = R.Audit.of(c, d, s)
      +inner = Bool.and(T.Audit.is_eq(a, t), Nat.is_le(T.Audit.extra(a), cap))
      +rest = L.and_r(R.Stops.all_open(R.Stops.tail(s)), inner, e)
      +le = L.and_r(T.Audit.is_eq(a, t), Nat.is_le(T.Audit.extra(a), cap), rest)
      +eq = audit_of(a, t, L.and_l(T.Audit.is_eq(a, t), Nat.is_le(T.Audit.extra(a), cap), rest))
      %eq : {Nat.is_le(T.Audit.extra(_), cap) == True{} : Bool}
      le

law open_tail:
  for +cap: Nat
  for +r: T.Route
  for +e: {R.Route.ok(cap, r) == True{} : Bool}
  {R.Stops.all_open(R.Stops.tail(T.Route.stops(r))) == True{} : Bool}

def open_tail(cap, r, e):
  PH.open_t(cap, r, e)

# Listed stops
# ------------

def Unstop(m: Maybe<&2, T.Stop>, +d: T.Stop) -> T.Stop:
  Maybe.default(&2, T.Stop, m, d)

law some_stop:
  for +a: T.Stop
  for +b: T.Stop
  for +e: {Some{a} == Some{b} : Maybe<&2, T.Stop>}
  {a == b : T.Stop}

def some_stop(a, b, e):
  Equal.cong(Maybe<&2, T.Stop>, T.Stop, m => Unstop(m, a), Some{a}, Some{b}, e)

def StopNone(m: Maybe<&2, T.Stop>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      Empty

law none_stop:
  for +a: T.Stop
  for +e: {None{} == Some{a} : Maybe<&2, T.Stop>}
  Empty

def none_stop(a, e):
  %e : StopNone(_)
  Unit{}

law has_cons:
  for +x: Nat
  for +t: List<&2, Nat>
  {R.Nats.has(x <> t, x) == True{} : Bool}

def has_cons(x, t):
  %Equal.sym(Bool, Nat.is_eq(x, x), True{}, L.eq_refl(x)) : {Bool.or(_, R.Nats.has(t, x)) == True{} : Bool}
  {==}

law has_skip:
  for +h: Nat
  for +t: List<&2, Nat>
  for +x: Nat
  for +e: {R.Nats.has(t, x) == True{} : Bool}
  {R.Nats.has(h <> t, x) == True{} : Bool}

def has_skip(h, t, x, e):
  %Equal.sym(Bool, R.Nats.has(t, x), True{}, e) : {Bool.or(Nat.is_eq(h, x), _) == True{} : Bool}
  L.or_true(Nat.is_eq(h, x))

law late_listed.t:
  for +c: Bool
  for +i: Nat
  for +r: List<&2, Nat>
  for +e: {c == True{} : Bool}
  {R.Nats.has(R.Stops.late.put(c, i, r), i) == True{} : Bool}

def late_listed.t(c, i, r, e):
  match c:
    case True{}:
      has_cons(i, r)
    case False{}:
      L.never({R.Nats.has(r, i) == True{} : Bool}, e)

law late_listed.s:
  for +c: Bool
  for +i: Nat
  for +x: Nat
  for +r: List<&2, Nat>
  for +e: {R.Nats.has(r, x) == True{} : Bool}
  {R.Nats.has(R.Stops.late.put(c, i, r), x) == True{} : Bool}

def late_listed.s(c, i, x, r, e):
  match c:
    case True{}:
      has_skip(i, r, x, e)
    case False{}:
      e

# A late stop is on the route's late list.
law late_listed:
  for +xs: ST()
  for +k: Nat
  for +s: T.Stop
  for +day: Nat
  for +at: {List.get(&2, T.Stop, xs, k) == Some{s} : Maybe<&2, T.Stop>}
  for +e: {Nat.is_gt(day, T.Appraisal.due(T.Stop.job(s))) == True{} : Bool}
  {R.Nats.has(R.Stops.late(xs, day), T.Stop.id(s)) == True{} : Bool}

def late_listed(xs, k, s, day, at, e):
  match xs k:
    case Nil{} _:
      Empty.absurd({R.Nats.has(Nil{}, T.Stop.id(s)) == True{} : Bool}, none_stop(s, at))
    case +h <> t 0n:
      +eq = some_stop(h, s, at)
      %eq : {R.Nats.has(R.Stops.late(h <> t, day), T.Stop.id(_)) == True{} : Bool}
      late_listed.t(Nat.is_gt(day, T.Appraisal.due(T.Stop.job(h))), T.Stop.id(h), R.Stops.late(t, day),
        %Equal.sym(T.Stop, h, s, eq) : {Nat.is_gt(day, T.Appraisal.due(T.Stop.job(_))) == True{} : Bool}
        e)
    case +h <> t 1n+p:
      late_listed.s(Nat.is_gt(day, T.Appraisal.due(T.Stop.job(h))), T.Stop.id(h), T.Stop.id(s), R.Stops.late(t, day),
        late_listed(t, p, s, day, at, e))

law outside_listed:
  for +xs: ST()
  for +k: Nat
  for +s: T.Stop
  for +zips: List<&2, Nat>
  for +at: {List.get(&2, T.Stop, xs, k) == Some{s} : Maybe<&2, T.Stop>}
  for +e: {R.Nats.has(zips, R.Stop.zip(s)) == False{} : Bool}
  {R.Nats.has(R.Stops.outside(xs, zips), T.Stop.id(s)) == True{} : Bool}

def outside_listed(xs, k, s, zips, at, e):
  match xs k:
    case Nil{} _:
      Empty.absurd({R.Nats.has(Nil{}, T.Stop.id(s)) == True{} : Bool}, none_stop(s, at))
    case +h <> t 0n:
      +eq = some_stop(h, s, at)
      %eq : {R.Nats.has(R.Stops.outside(h <> t, zips), T.Stop.id(_)) == True{} : Bool}
      late_listed.t(Bool.not(R.Nats.has(zips, R.Stop.zip(h))), T.Stop.id(h), R.Stops.outside(t, zips),
        L.not_of(R.Nats.has(zips, R.Stop.zip(h)),
          %Equal.sym(T.Stop, h, s, eq) : {R.Nats.has(zips, R.Stop.zip(_)) == False{} : Bool}
          e))
    case +h <> t 1n+p:
      late_listed.s(Bool.not(R.Nats.has(zips, R.Stop.zip(h))), T.Stop.id(h), T.Stop.id(s), R.Stops.outside(t, zips),
        outside_listed(t, p, s, zips, at, e))

# Counts on one route are bounded by the whole plan
# -------------------------------------------------

law jc_le_rc:
  for +a: T.Appraisal
  for +routes: RL()
  for +n: Nat
  for +r: T.Route
  for +at: At(routes, n, r)
  {Nat.is_le(JC(a, T.Route.stops(r)), PP.RC(a, routes)) == True{} : Bool}

def jc_le_rc(a, routes, n, r, at):
  match routes n:
    case Nil{} _:
      Empty.absurd({Nat.is_le(JC(a, T.Route.stops(r)), PP.RC(a, Nil{})) == True{} : Bool}, none_is_not_some(r, at))
    case +h <> +t 0n:
      %Equal.sym(Nat, PP.RC(a, h <> t), Nat.add(JC(a, T.Route.stops(h)), PP.RC(a, t)), PP.rc_cons(a, h, t)) : {Nat.is_le(JC(a, T.Route.stops(r)), _) == True{} : Bool}
      %some_route(h, r, at) : {Nat.is_le(JC(a, T.Route.stops(_)), Nat.add(JC(a, T.Route.stops(h)), PP.RC(a, t))) == True{} : Bool}
      L.le_add_l(JC(a, T.Route.stops(h)), PP.RC(a, t))
    case +h <> +t 1n+p:
      %Equal.sym(Nat, PP.RC(a, h <> t), Nat.add(JC(a, T.Route.stops(h)), PP.RC(a, t)), PP.rc_cons(a, h, t)) : {Nat.is_le(JC(a, T.Route.stops(r)), _) == True{} : Bool}
      L.le_trans(JC(a, T.Route.stops(r)), PP.RC(a, t), Nat.add(JC(a, T.Route.stops(h)), PP.RC(a, t)),
        jc_le_rc(a, t, p, r, at), L.le_add_r(JC(a, T.Route.stops(h)), PP.RC(a, t)))

law once_on_route:
  for +a: T.Appraisal
  for +inst: T.Instance
  for +plan: T.Plan
  for +n: Nat
  for +r: T.Route
  for +ev: {P.Plan.valid(inst, plan) == True{} : Bool}
  for +at: At(T.Plan.routes(plan), n, r)
  {Nat.is_le(JC(a, T.Route.stops(r)), 1n) == True{} : Bool}

def once_on_route(a, inst, plan, n, r, ev, at):
  +routes = T.Plan.routes(plan)
  +rest = Nat.add(J.count(a, T.Plan.backlog(plan)), PP.EC(a, T.Plan.exceptions(plan)))
  +c = J.count(a, T.Instance.jobs(inst))
  L.le_trans(JC(a, T.Route.stops(r)), PP.RC(a, routes), 1n, jc_le_rc(a, routes, n, r, at),
    L.le_trans(PP.RC(a, routes), Nat.add(PP.RC(a, routes), rest), 1n, L.le_add_l(PP.RC(a, routes), rest),
      %PP.placed_count(a, plan) : {Nat.is_le(_, 1n) == True{} : Bool}
      %Equal.sym(Nat, J.count(a, P.Plan.placed(plan)), c, PP.count_valid(a, inst, plan, ev)) : {Nat.is_le(_, 1n) == True{} : Bool}
      PJ.rising_once(a, T.Instance.jobs(inst), 0n, PP.v_inst(inst, plan, ev))))

# Slots
# -----

law slot_lt_trans:
  for +a: P.Slot
  for +b: P.Slot
  for +c: P.Slot
  for +ab: {P.Slot.lt(a, b) == True{} : Bool}
  for +bc: {P.Slot.lt(b, c) == True{} : Bool}
  {P.Slot.lt(a, c) == True{} : Bool}

def slot_lt_trans(a, b, c, ab, bc):
  match a b c:
    case P.Slot{c1, d1} P.Slot{c2, d2} P.Slot{c3, d3}:
      +l12 = Nat.is_lt(c1, c2)
      +l23 = Nat.is_lt(c2, c3)
      +e12 = Bool.and(Nat.is_eq(c1, c2), Nat.is_lt(d1, d2))
      +e23 = Bool.and(Nat.is_eq(c2, c3), Nat.is_lt(d2, d3))
      +goal = Bool.or(Nat.is_lt(c1, c3), Bool.and(Nat.is_eq(c1, c3), Nat.is_lt(d1, d3)))
      L.cases(l12, {goal == True{} : Bool},
        +x =>
          L.cases(l23, {goal == True{} : Bool},
            +y => L.or_left(Nat.is_lt(c1, c3), Bool.and(Nat.is_eq(c1, c3), Nat.is_lt(d1, d3)), L.lt_trans(c1, c2, c3, x, y)),
            +y =>
              +e = L.eq_of(c2, c3, L.and_l(Nat.is_eq(c2, c3), Nat.is_lt(d2, d3), L.or_rest(l23, e23, bc, y)))
              L.or_left(Nat.is_lt(c1, c3), Bool.and(Nat.is_eq(c1, c3), Nat.is_lt(d1, d3)),
                %e : {Nat.is_lt(c1, _) == True{} : Bool}
                x)),
        +x =>
          +p = L.or_rest(l12, e12, ab, x)
          +eq = L.eq_of(c1, c2, L.and_l(Nat.is_eq(c1, c2), Nat.is_lt(d1, d2), p))
          +d12 = L.and_r(Nat.is_eq(c1, c2), Nat.is_lt(d1, d2), p)
          L.cases(l23, {goal == True{} : Bool},
            +y => L.or_left(Nat.is_lt(c1, c3), Bool.and(Nat.is_eq(c1, c3), Nat.is_lt(d1, d3)),
              %Equal.sym(Nat, c1, c2, eq) : {Nat.is_lt(_, c3) == True{} : Bool}
              y),
            +y =>
              +q = L.or_rest(l23, e23, bc, y)
              +eq2 = L.and_l(Nat.is_eq(c2, c3), Nat.is_lt(d2, d3), q)
              L.or_right(Nat.is_lt(c1, c3), Bool.and(Nat.is_eq(c1, c3), Nat.is_lt(d1, d3)),
                L.and_i(Nat.is_eq(c1, c3), Nat.is_lt(d1, d3),
                  %Equal.sym(Nat, c1, c2, eq) : {Nat.is_eq(_, c3) == True{} : Bool}
                  eq2,
                  L.lt_trans(d1, d2, d3, d12, L.and_r(Nat.is_eq(c2, c3), Nat.is_lt(d2, d3), q))))))

law slot_lt_irrefl:
  for +a: P.Slot
  {P.Slot.lt(a, a) == False{} : Bool}

def slot_lt_irrefl(a):
  match a:
    case P.Slot{c, d}:
      %Equal.sym(Bool, Nat.is_lt(c, c), False{}, L.lt_self(c)) : {Bool.or(_, Bool.and(Nat.is_eq(c, c), Nat.is_lt(d, d))) == False{} : Bool}
      %Equal.sym(Bool, Nat.is_lt(d, d), False{}, L.lt_self(d)) : {Bool.and(Nat.is_eq(c, c), _) == False{} : Bool}
      L.and_false(Nat.is_eq(c, c))

def SL() -> Data:
  List<&2, P.Slot>

def SlotNone(m: Maybe<&2, P.Slot>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      Empty

law none_slot:
  for +a: P.Slot
  for +e: {None{} == Some{a} : Maybe<&2, P.Slot>}
  Empty

def none_slot(a, e):
  %e : SlotNone(_)
  Unit{}

law some_slot:
  for +a: P.Slot
  for +b: P.Slot
  for +e: {Some{a} == Some{b} : Maybe<&2, P.Slot>}
  {a == b : P.Slot}

def some_slot(a, b, e):
  Equal.cong(Maybe<&2, P.Slot>, P.Slot, m => Maybe.default(&2, P.Slot, m, a), Some{a}, Some{b}, e)

law after_lo:
  for +xs: SL()
  for +lo: P.Slot
  for +k: Nat
  for +s: P.Slot
  for +ea: {P.Slots.after(xs, lo) == True{} : Bool}
  for +at: {List.get(&2, P.Slot, xs, k) == Some{s} : Maybe<&2, P.Slot>}
  {P.Slot.lt(lo, s) == True{} : Bool}

def after_lo(xs, lo, k, s, ea, at):
  match xs k:
    case Nil{} _:
      Empty.absurd({P.Slot.lt(lo, s) == True{} : Bool}, none_slot(s, at))
    case +h <> t 0n:
      %some_slot(h, s, at) : {P.Slot.lt(lo, _) == True{} : Bool}
      L.and_l(P.Slot.lt(lo, h), P.Slots.after(t, h), ea)
    case +h <> t 1n+p:
      slot_lt_trans(lo, h, s, L.and_l(P.Slot.lt(lo, h), P.Slots.after(t, h), ea),
        after_lo(t, h, p, s, L.and_r(P.Slot.lt(lo, h), P.Slots.after(t, h), ea), at))

law sorted_tail:
  for +h: P.Slot
  for +t: SL()
  for +e: {P.Slots.sorted(h <> t) == True{} : Bool}
  {P.Slots.sorted(t) == True{} : Bool}

def sorted_tail(h, t, e):
  match t:
    case Nil{}:
      {==}
    case +x <> r:
      L.and_r(P.Slot.lt(h, x), P.Slots.after(r, x), e)

law sorted_lt:
  for +xs: SL()
  for +n: Nat
  for +k: Nat
  for +a: P.Slot
  for +b: P.Slot
  for +es: {P.Slots.sorted(xs) == True{} : Bool}
  for +lt: {Nat.is_lt(n, k) == True{} : Bool}
  for +ea: {List.get(&2, P.Slot, xs, n) == Some{a} : Maybe<&2, P.Slot>}
  for +eb: {List.get(&2, P.Slot, xs, k) == Some{b} : Maybe<&2, P.Slot>}
  {P.Slot.lt(a, b) == True{} : Bool}

def sorted_lt(xs, n, k, a, b, es, lt, ea, eb):
  match xs n k:
    case Nil{} _ _:
      Empty.absurd({P.Slot.lt(a, b) == True{} : Bool}, none_slot(a, ea))
    case +h <> t 0n 0n:
      L.never({P.Slot.lt(a, b) == True{} : Bool}, lt)
    case +h <> t 0n 1n+q:
      %some_slot(h, a, ea) : {P.Slot.lt(_, b) == True{} : Bool}
      after_lo(t, h, q, b, es, eb)
    case +h <> t 1n+p 0n:
      L.never({P.Slot.lt(a, b) == True{} : Bool}, lt)
    case +h <> t 1n+p 1n+q:
      sorted_lt(t, p, q, a, b, sorted_tail(h, t, es), lt, ea, eb)

law get_slot:
  for +routes: RL()
  for +n: Nat
  for +r: T.Route
  for +at: At(routes, n, r)
  {List.get(&2, P.Slot, P.Routes.slots(routes), n) == Some{P.Route.slot(r)} : Maybe<&2, P.Slot>}

def get_slot(routes, n, r, at):
  match routes n:
    case Nil{} _:
      Empty.absurd({List.get(&2, P.Slot, Nil{}, n) == Some{P.Route.slot(r)} : Maybe<&2, P.Slot>}, none_is_not_some(r, at))
    case +h <> t 0n:
      %some_route(h, r, at) : {Some{P.Route.slot(h)} == Some{P.Route.slot(_)} : Maybe<&2, P.Slot>}
      {==}
    case +h <> t 1n+p:
      get_slot(t, p, r, at)

# Finding a contractor
# --------------------

law crew_found.next:
  for +h: T.Contractor
  for +t: Crews()
  for +c: T.Contractor
  for p: Exists(Nat, i => {List.get(&2, T.Contractor, t, i) == Some{c} : Maybe<&2, T.Contractor>})
  Exists(Nat, i => {List.get(&2, T.Contractor, h <> t, i) == Some{c} : Maybe<&2, T.Contractor>})

def crew_found.next(h, t, c, p):
  (i, e) = p
  (1n+i, e)

law crew_of.go:
  for +i1: Nat
  for +i2: Nat
  for +h1: T.Point
  for +h2: T.Point
  for +z1: List<&2, Nat>
  for +z2: List<&2, Nat>
  for +m1: Nat
  for +m2: Nat
  for +d1: List<&2, Nat>
  for +d2: List<&2, Nat>
  for +ei: {i1 == i2 : Nat}
  for +eh: {h1 == h2 : T.Point}
  for +ez: {z1 == z2 : List<&2, Nat>}
  for +em: {m1 == m2 : Nat}
  for +ed: {d1 == d2 : List<&2, Nat>}
  {T.Contractor{i1, h1, z1, m1, d1} == T.Contractor{i2, h2, z2, m2, d2} : T.Contractor}

def crew_of.go(i1, i2, h1, h2, z1, z2, m1, m2, d1, d2, ei, eh, ez, em, ed):
  %ei : {T.Contractor{i1, h1, z1, m1, d1} == T.Contractor{_, h2, z2, m2, d2} : T.Contractor}
  %eh : {T.Contractor{i1, h1, z1, m1, d1} == T.Contractor{i1, _, z2, m2, d2} : T.Contractor}
  %ez : {T.Contractor{i1, h1, z1, m1, d1} == T.Contractor{i1, h1, _, m2, d2} : T.Contractor}
  %em : {T.Contractor{i1, h1, z1, m1, d1} == T.Contractor{i1, h1, z1, _, d2} : T.Contractor}
  %ed : {T.Contractor{i1, h1, z1, m1, d1} == T.Contractor{i1, h1, z1, m1, _} : T.Contractor}
  {==}

law crew_of:
  for +a: T.Contractor
  for +b: T.Contractor
  for +e: {T.Contractor.is_eq(a, b) == True{} : Bool}
  {a == b : T.Contractor}

def crew_of(a, b, e):
  match a b:
    case T.Contractor{i1, h1, z1, m1, d1} T.Contractor{i2, h2, z2, m2, d2}:
      +r3 = Bool.and(Nat.is_eq(m1, m2), T.Nats.is_eq(d1, d2))
      +r2 = Bool.and(T.Nats.is_eq(z1, z2), r3)
      +r1 = Bool.and(T.Point.is_eq(h1, h2), r2)
      +s1 = L.and_r(Nat.is_eq(i1, i2), r1, e)
      +s2 = L.and_r(T.Point.is_eq(h1, h2), r2, s1)
      +s3 = L.and_r(T.Nats.is_eq(z1, z2), r3, s2)
      crew_of.go(i1, i2, h1, h2, z1, z2, m1, m2, d1, d2,
        L.eq_of(i1, i2, L.and_l(Nat.is_eq(i1, i2), r1, e)),
        PJ.point_of(h1, h2, L.and_l(T.Point.is_eq(h1, h2), r2, s1)),
        L.nats_of(z1, z2, L.and_l(T.Nats.is_eq(z1, z2), r3, s2)),
        L.eq_of(m1, m2, L.and_l(Nat.is_eq(m1, m2), T.Nats.is_eq(d1, d2), s3)),
        L.nats_of(d1, d2, L.and_r(Nat.is_eq(m1, m2), T.Nats.is_eq(d1, d2), s3)))

# Crews.has means the contractor really is in the list, at some index.
law crew_found:
  for +crews: Crews()
  for +c: T.Contractor
  for +e: {P.Crews.has(crews, c) == True{} : Bool}
  exs i: Nat
  {List.get(&2, T.Contractor, crews, i) == Some{c} : Maybe<&2, T.Contractor>}

def crew_found(crews, c, e):
  match crews:
    case Nil{}:
      L.never(Exists(Nat, i => {List.get(&2, T.Contractor, Nil{}, i) == Some{c} : Maybe<&2, T.Contractor>}), e)
    case +h <> +t:
      +a = T.Contractor.is_eq(h, c)
      +b = P.Crews.has(t, c)
      L.cases(a, Exists(Nat, i => {List.get(&2, T.Contractor, h <> t, i) == Some{c} : Maybe<&2, T.Contractor>}),
        +x => (0n, %crew_of(h, c, x) : {Some{h} == Some{_} : Maybe<&2, T.Contractor>}
          {==}),
        +x => crew_found.next(h, t, c, crew_found(t, c, L.or_rest(a, b, e, x))))

# Loops
# -----

law last_home:
  for +stops: ST()
  for +x: T.Point
  for +home: T.Point
  {List.last.go(&2, T.Point, R.Route.path.go(stops, home), x) == home : T.Point}

def last_home(stops, x, home):
  match stops:
    case Nil{}:
      {==}
    case +s <> r:
      last_home(r, R.Stop.site(s), home)
