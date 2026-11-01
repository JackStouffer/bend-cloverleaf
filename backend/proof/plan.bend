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

# Whole plans: what a plan places, the parts of Plan.valid, and why an edit to
# the routes leaves a plan valid.

def ST() -> Data:
  List<&2, T.Stop>

def AL() -> Data:
  List<&2, T.Appraisal>

def RL() -> Data:
  List<&2, T.Route>

def XL() -> Data:
  List<&2, T.Exception>

def JC(+a: T.Appraisal, xs: ST()) -> Nat:
  J.count(a, R.Stops.jobs(xs))

def RC(+a: T.Appraisal, routes: RL()) -> Nat:
  J.count(a, P.Routes.jobs(routes))

def EC(+a: T.Appraisal, ex: XL()) -> Nat:
  J.count(a, P.Exceptions.jobs(ex))

law rc_cons:
  for +a: T.Appraisal
  for +r: T.Route
  for +t: RL()
  {RC(a, r <> t) == Nat.add(JC(a, T.Route.stops(r)), RC(a, t)) : Nat}

def rc_cons(a, r, t):
  PJ.count_append(a, R.Stops.jobs(T.Route.stops(r)), P.Routes.jobs(t))

law placed_count:
  for +a: T.Appraisal
  for +plan: T.Plan
  {J.count(a, P.Plan.placed(plan)) == Nat.add(RC(a, T.Plan.routes(plan)), Nat.add(J.count(a, T.Plan.backlog(plan)), EC(a, T.Plan.exceptions(plan)))) : Nat}

def placed_count(a, plan):
  +rj = P.Routes.jobs(T.Plan.routes(plan))
  +b = T.Plan.backlog(plan)
  +ej = P.Exceptions.jobs(T.Plan.exceptions(plan))
  Equal.trans(Nat, J.count(a, List.append(&2, T.Appraisal, rj, List.append(&2, T.Appraisal, b, ej))),
    Nat.add(J.count(a, rj), J.count(a, List.append(&2, T.Appraisal, b, ej))),
    Nat.add(J.count(a, rj), Nat.add(J.count(a, b), J.count(a, ej))),
    PJ.count_append(a, rj, List.append(&2, T.Appraisal, b, ej)),
    L.add_r(J.count(a, rj), J.count(a, List.append(&2, T.Appraisal, b, ej)), Nat.add(J.count(a, b), J.count(a, ej)),
      PJ.count_append(a, b, ej)))

law count_with:
  for +a: T.Appraisal
  for +rs: RL()
  for +shed: ST()
  for +b: AL()
  for +ex: XL()
  {J.count(a, P.Plan.placed(H.Plan.with(rs, shed, b, ex))) == Nat.add(Nat.add(RC(a, rs), JC(a, shed)), Nat.add(J.count(a, b), EC(a, ex))) : Nat}

def count_with(a, rs, shed, b, ex):
  +p = H.Plan.with(rs, shed, b, ex)
  +js = R.Stops.jobs(shed)
  Equal.trans(Nat, J.count(a, P.Plan.placed(p)), Nat.add(RC(a, rs), Nat.add(J.count(a, List.append(&2, T.Appraisal, js, b)), EC(a, ex))),
    Nat.add(Nat.add(RC(a, rs), JC(a, shed)), Nat.add(J.count(a, b), EC(a, ex))),
    placed_count(a, p),
    Equal.trans(Nat, Nat.add(RC(a, rs), Nat.add(J.count(a, List.append(&2, T.Appraisal, js, b)), EC(a, ex))),
      Nat.add(RC(a, rs), Nat.add(Nat.add(JC(a, shed), J.count(a, b)), EC(a, ex))),
      Nat.add(Nat.add(RC(a, rs), JC(a, shed)), Nat.add(J.count(a, b), EC(a, ex))),
      L.add_r(RC(a, rs), Nat.add(J.count(a, List.append(&2, T.Appraisal, js, b)), EC(a, ex)), Nat.add(Nat.add(JC(a, shed), J.count(a, b)), EC(a, ex)),
        L.add_l(J.count(a, List.append(&2, T.Appraisal, js, b)), Nat.add(JC(a, shed), J.count(a, b)), EC(a, ex), PJ.count_append(a, js, b))),
      L.shed_assoc(RC(a, rs), JC(a, shed), J.count(a, b), EC(a, ex))))

# Edited lists
# ------------

law edited_routes:
  for +s: R.Step
  for +e: H.Edited
  {H.Edited.routes(H.Edited.cons(s, e)) == R.Step.route(s) <> H.Edited.routes(e) : RL()}

def edited_routes(s, e):
  match s e:
    case R.Step{r, x} H.Edited{rs, xs}:
      {==}

law edited_shed:
  for +s: R.Step
  for +e: H.Edited
  {H.Edited.shed(H.Edited.cons(s, e)) == R.Stops.append(R.Step.shed(s), H.Edited.shed(e)) : ST()}

def edited_shed(s, e):
  match s e:
    case R.Step{r, x} H.Edited{rs, xs}:
      {==}

def EB(+a: T.Appraisal, +e: H.Edited) -> Nat:
  Nat.add(RC(a, H.Edited.routes(e)), JC(a, H.Edited.shed(e)))

law eb_cons:
  for +a: T.Appraisal
  for +s: R.Step
  for +e: H.Edited
  {EB(a, H.Edited.cons(s, e)) == Nat.add(PH.Bag(a, s), EB(a, e)) : Nat}

def eb_cons(a, s, e):
  +c = H.Edited.cons(s, e)
  +r = R.Step.route(s)
  +x = R.Step.shed(s)
  +rs = H.Edited.routes(e)
  +xs = H.Edited.shed(e)
  %Equal.sym(RL(), H.Edited.routes(c), r <> rs, edited_routes(s, e)) : {Nat.add(RC(a, _), JC(a, H.Edited.shed(c))) == Nat.add(PH.Bag(a, s), EB(a, e)) : Nat}
  %Equal.sym(ST(), H.Edited.shed(c), R.Stops.append(x, xs), edited_shed(s, e)) : {Nat.add(RC(a, r <> rs), JC(a, _)) == Nat.add(PH.Bag(a, s), EB(a, e)) : Nat}
  Equal.trans(Nat, Nat.add(RC(a, r <> rs), JC(a, R.Stops.append(x, xs))), Nat.add(Nat.add(JC(a, T.Route.stops(r)), RC(a, rs)), JC(a, R.Stops.append(x, xs))),
    Nat.add(PH.Bag(a, s), EB(a, e)),
    L.add_l(RC(a, r <> rs), Nat.add(JC(a, T.Route.stops(r)), RC(a, rs)), JC(a, R.Stops.append(x, xs)), rc_cons(a, r, rs)),
    Equal.trans(Nat, Nat.add(Nat.add(JC(a, T.Route.stops(r)), RC(a, rs)), JC(a, R.Stops.append(x, xs))),
      Nat.add(Nat.add(JC(a, T.Route.stops(r)), RC(a, rs)), Nat.add(JC(a, x), JC(a, xs))), Nat.add(PH.Bag(a, s), EB(a, e)),
      L.add_r(Nat.add(JC(a, T.Route.stops(r)), RC(a, rs)), JC(a, R.Stops.append(x, xs)), Nat.add(JC(a, x), JC(a, xs)), PR.jc_append(a, x, xs)),
      L.add_four(JC(a, T.Route.stops(r)), RC(a, rs), JC(a, x), JC(a, xs))))

law eb_apply:
  for +a: T.Appraisal
  for +routes: RL()
  for +cap: Nat
  for +e: H.Edit
  {EB(a, H.Routes.apply(routes, cap, e)) == RC(a, routes) : Nat}

def eb_apply(a, routes, cap, e):
  match routes:
    case Nil{}:
      {==}
    case +r <> t:
      +s = H.Route.apply(cap, e, r)
      +rest = H.Routes.apply(t, cap, e)
      Equal.trans(Nat, EB(a, H.Edited.cons(s, rest)), Nat.add(PH.Bag(a, s), EB(a, rest)), RC(a, r <> t),
        eb_cons(a, s, rest),
        Equal.trans(Nat, Nat.add(PH.Bag(a, s), EB(a, rest)), Nat.add(JC(a, T.Route.stops(r)), EB(a, rest)), RC(a, r <> t),
          L.add_l(PH.Bag(a, s), JC(a, T.Route.stops(r)), EB(a, rest), PH.jc_apply(a, cap, e, r)),
          Equal.trans(Nat, Nat.add(JC(a, T.Route.stops(r)), EB(a, rest)), Nat.add(JC(a, T.Route.stops(r)), RC(a, t)), RC(a, r <> t),
            L.add_r(JC(a, T.Route.stops(r)), EB(a, rest), RC(a, t), eb_apply(a, t, cap, e)),
            Equal.sym(Nat, RC(a, r <> t), Nat.add(JC(a, T.Route.stops(r)), RC(a, t)), rc_cons(a, r, t)))))

law slot_step:
  for +s: R.Step
  for +r: T.Route
  for +ec: {T.Route.crew(R.Step.route(s)) == T.Route.crew(r) : T.Contractor}
  for +ed: {T.Route.day(R.Step.route(s)) == T.Route.day(r) : Nat}
  {P.Route.slot(R.Step.route(s)) == P.Route.slot(r) : P.Slot}

def slot_step(s, r, ec, ed):
  +q = R.Step.route(s)
  %ec : {P.Slot{T.Contractor.id(T.Route.crew(q)), T.Route.day(q)} == P.Slot{T.Contractor.id(_), T.Route.day(r)} : P.Slot}
  %ed : {P.Slot{T.Contractor.id(T.Route.crew(q)), T.Route.day(q)} == P.Slot{T.Contractor.id(T.Route.crew(q)), _} : P.Slot}
  {==}

def EC1(+s: R.Step, +r: T.Route) -> Type:
  {T.Route.crew(R.Step.route(s)) == T.Route.crew(r) : T.Contractor}

def ED1(+s: R.Step, +r: T.Route) -> Type:
  {T.Route.day(R.Step.route(s)) == T.Route.day(r) : Nat}

law crew_apply:
  for +cap: Nat
  for +e: H.Edit
  for +r: T.Route
  EC1(H.Route.apply(cap, e, r), r)

def crew_apply(cap, e, r):
  Pair.fst(EC1(H.Route.apply(cap, e, r), r), ED1(H.Route.apply(cap, e, r), r), PH.keeps_apply(cap, e, r))

law day_apply:
  for +cap: Nat
  for +e: H.Edit
  for +r: T.Route
  ED1(H.Route.apply(cap, e, r), r)

def day_apply(cap, e, r):
  Pair.snd(EC1(H.Route.apply(cap, e, r), r), ED1(H.Route.apply(cap, e, r), r), PH.keeps_apply(cap, e, r))

law fine_step:
  for +crews: List<&2, T.Contractor>
  for +cap: Nat
  for +s: R.Step
  for +r: T.Route
  for +ef: {P.Route.fine(crews, cap, r) == True{} : Bool}
  for +ec: {T.Route.crew(R.Step.route(s)) == T.Route.crew(r) : T.Contractor}
  for +eo: {R.Route.ok(cap, R.Step.route(s)) == True{} : Bool}
  {P.Route.fine(crews, cap, R.Step.route(s)) == True{} : Bool}

def fine_step(crews, cap, s, r, ef, ec, eo):
  +q = R.Step.route(s)
  L.and_i(P.Crews.has(crews, T.Route.crew(q)), R.Route.ok(cap, q),
    %Equal.sym(T.Contractor, T.Route.crew(q), T.Route.crew(r), ec) : {P.Crews.has(crews, _) == True{} : Bool}
    L.and_l(P.Crews.has(crews, T.Route.crew(r)), R.Route.ok(cap, r), ef),
    eo)

law ok_of_fine:
  for +crews: List<&2, T.Contractor>
  for +cap: Nat
  for +r: T.Route
  for +ef: {P.Route.fine(crews, cap, r) == True{} : Bool}
  {R.Route.ok(cap, r) == True{} : Bool}

def ok_of_fine(crews, cap, r, ef):
  L.and_r(P.Crews.has(crews, T.Route.crew(r)), R.Route.ok(cap, r), ef)

law routes_head:
  for +r: T.Route
  for +t: RL()
  for +crews: List<&2, T.Contractor>
  for +cap: Nat
  for +e: {P.Routes.ok(r <> t, crews, cap) == True{} : Bool}
  {P.Route.fine(crews, cap, r) == True{} : Bool}

def routes_head(r, t, crews, cap, e):
  L.and_l(P.Route.fine(crews, cap, r), P.Routes.ok(t, crews, cap), e)

law routes_tail:
  for +r: T.Route
  for +t: RL()
  for +crews: List<&2, T.Contractor>
  for +cap: Nat
  for +e: {P.Routes.ok(r <> t, crews, cap) == True{} : Bool}
  {P.Routes.ok(t, crews, cap) == True{} : Bool}

def routes_tail(r, t, crews, cap, e):
  L.and_r(P.Route.fine(crews, cap, r), P.Routes.ok(t, crews, cap), e)

law routes_cons:
  for +s: R.Step
  for +rest: H.Edited
  for +crews: List<&2, T.Contractor>
  for +cap: Nat
  for +ef: {P.Route.fine(crews, cap, R.Step.route(s)) == True{} : Bool}
  for +et: {P.Routes.ok(H.Edited.routes(rest), crews, cap) == True{} : Bool}
  {P.Routes.ok(H.Edited.routes(H.Edited.cons(s, rest)), crews, cap) == True{} : Bool}

def routes_cons(s, rest, crews, cap, ef, et):
  +q = R.Step.route(s)
  %Equal.sym(RL(), H.Edited.routes(H.Edited.cons(s, rest)), q <> H.Edited.routes(rest), edited_routes(s, rest)) : {P.Routes.ok(_, crews, cap) == True{} : Bool}
  L.and_i(P.Route.fine(crews, cap, q), P.Routes.ok(H.Edited.routes(rest), crews, cap), ef, et)

law ok_routes:
  for +routes: RL()
  for +crews: List<&2, T.Contractor>
  for +cap: Nat
  for +e: H.Edit
  for +er: {P.Routes.ok(routes, crews, cap) == True{} : Bool}
  {P.Routes.ok(H.Edited.routes(H.Routes.apply(routes, cap, e)), crews, cap) == True{} : Bool}

def ok_routes(routes, crews, cap, e, er):
  match routes:
    case Nil{}:
      {==}
    case +r <> t:
      +s = H.Route.apply(cap, e, r)
      +hd = routes_head(r, t, crews, cap, er)
      routes_cons(s, H.Routes.apply(t, cap, e), crews, cap,
        fine_step(crews, cap, s, r, hd, crew_apply(cap, e, r), PH.ok_apply(cap, e, r, ok_of_fine(crews, cap, r, hd))),
        ok_routes(t, crews, cap, e, routes_tail(r, t, crews, cap, er)))

law slots_cons:
  for +s: R.Step
  for +r: T.Route
  for +rest: H.Edited
  for +t: RL()
  for +ec: {T.Route.crew(R.Step.route(s)) == T.Route.crew(r) : T.Contractor}
  for +ed: {T.Route.day(R.Step.route(s)) == T.Route.day(r) : Nat}
  for +eh: {P.Routes.slots(H.Edited.routes(rest)) == P.Routes.slots(t) : List<&2, P.Slot>}
  {P.Routes.slots(H.Edited.routes(H.Edited.cons(s, rest))) == P.Routes.slots(r <> t) : List<&2, P.Slot>}

def slots_cons(s, r, rest, t, ec, ed, eh):
  +q = R.Step.route(s)
  %Equal.sym(RL(), H.Edited.routes(H.Edited.cons(s, rest)), q <> H.Edited.routes(rest), edited_routes(s, rest)) : {P.Routes.slots(_) == P.Routes.slots(r <> t) : List<&2, P.Slot>}
  %Equal.sym(P.Slot, P.Route.slot(q), P.Route.slot(r), slot_step(s, r, ec, ed)) : {_ <> P.Routes.slots(H.Edited.routes(rest)) == P.Route.slot(r) <> P.Routes.slots(t) : List<&2, P.Slot>}
  %eh : {P.Route.slot(r) <> P.Routes.slots(H.Edited.routes(rest)) == P.Route.slot(r) <> _ : List<&2, P.Slot>}
  {==}

law slots_apply:
  for +routes: RL()
  for +cap: Nat
  for +e: H.Edit
  {P.Routes.slots(H.Edited.routes(H.Routes.apply(routes, cap, e))) == P.Routes.slots(routes) : List<&2, P.Slot>}

def slots_apply(routes, cap, e):
  match routes:
    case Nil{}:
      {==}
    case +r <> t:
      slots_cons(H.Route.apply(cap, e, r), r, H.Routes.apply(t, cap, e), t, crew_apply(cap, e, r), day_apply(cap, e, r), slots_apply(t, cap, e))

law locked_cons:
  for +s: R.Step
  for +rest: H.Edited
  {P.Routes.locked(H.Edited.routes(H.Edited.cons(s, rest))) == PH.Lk(s) <> P.Routes.locked(H.Edited.routes(rest)) : List<&2, ST()>}

def locked_cons(s, rest):
  %Equal.sym(RL(), H.Edited.routes(H.Edited.cons(s, rest)), R.Step.route(s) <> H.Edited.routes(rest), edited_routes(s, rest)) : {P.Routes.locked(_) == PH.Lk(s) <> P.Routes.locked(H.Edited.routes(rest)) : List<&2, ST()>}
  {==}

law locked_routes:
  for +routes: RL()
  for +crews: List<&2, T.Contractor>
  for +cap: Nat
  for +e: H.Edit
  for +er: {P.Routes.ok(routes, crews, cap) == True{} : Bool}
  for +eh: {PH.Heals(e) == True{} : Bool}
  {P.Routes.locked(H.Edited.routes(H.Routes.apply(routes, cap, e))) == P.Routes.locked(routes) : List<&2, ST()>}

def locked_routes(routes, crews, cap, e, er, eh):
  match routes:
    case Nil{}:
      {==}
    case +r <> t:
      +s = H.Route.apply(cap, e, r)
      +rest = H.Routes.apply(t, cap, e)
      %Equal.sym(List<&2, ST()>, P.Routes.locked(H.Edited.routes(H.Edited.cons(s, rest))), PH.Lk(s) <> P.Routes.locked(H.Edited.routes(rest)), locked_cons(s, rest)) : {_ == P.Routes.locked(r <> t) : List<&2, ST()>}
      %PH.locked_apply(cap, e, r, ok_of_fine(crews, cap, r, routes_head(r, t, crews, cap, er)), eh) : {PH.Lk(s) <> P.Routes.locked(H.Edited.routes(rest)) == _ <> P.Routes.locked(t) : List<&2, ST()>}
      %locked_routes(t, crews, cap, e, routes_tail(r, t, crews, cap, er), eh) : {PH.Lk(s) <> P.Routes.locked(H.Edited.routes(rest)) == PH.Lk(s) <> _ : List<&2, ST()>}
      {==}

# Plan.edit
# ---------

law count_edit:
  for +a: T.Appraisal
  for +cap: Nat
  for +e: H.Edit
  for +plan: T.Plan
  {J.count(a, P.Plan.placed(H.Plan.edit(cap, e, plan))) == J.count(a, P.Plan.placed(plan)) : Nat}

def count_edit(a, cap, e, plan):
  +routes = T.Plan.routes(plan)
  +b = T.Plan.backlog(plan)
  +ex = T.Plan.exceptions(plan)
  +done = H.Routes.apply(routes, cap, e)
  Equal.trans(Nat, J.count(a, P.Plan.placed(H.Plan.with(H.Edited.routes(done), H.Edited.shed(done), b, ex))),
    Nat.add(EB(a, done), Nat.add(J.count(a, b), EC(a, ex))), J.count(a, P.Plan.placed(plan)),
    count_with(a, H.Edited.routes(done), H.Edited.shed(done), b, ex),
    Equal.trans(Nat, Nat.add(EB(a, done), Nat.add(J.count(a, b), EC(a, ex))), Nat.add(RC(a, routes), Nat.add(J.count(a, b), EC(a, ex))),
      J.count(a, P.Plan.placed(plan)),
      L.add_l(EB(a, done), RC(a, routes), Nat.add(J.count(a, b), EC(a, ex)), eb_apply(a, routes, cap, e)),
      Equal.sym(Nat, J.count(a, P.Plan.placed(plan)), Nat.add(RC(a, routes), Nat.add(J.count(a, b), EC(a, ex))), placed_count(a, plan))))

# Plan.valid, part by part
# ------------------------

def Routes3(+inst: T.Instance, +plan: T.Plan) -> Bool:
  P.Routes.ok(T.Plan.routes(plan), T.Instance.crews(inst), T.Instance.cap(inst))

def Rest2(+inst: T.Instance, +plan: T.Plan) -> Bool:
  Bool.and(P.Slots.sorted(P.Routes.slots(T.Plan.routes(plan))), Routes3(inst, plan))

def InState(+inst: T.Instance) -> Bool:
  Bool.and(J.in_state(T.Instance.jobs(inst), T.Instance.state(inst)), P.Crews.in_state(T.Instance.crews(inst), T.Instance.state(inst)))

def Rest1(+inst: T.Instance, +plan: T.Plan) -> Bool:
  Bool.and(P.Plan.partition_ok(inst, plan), Rest2(inst, plan))

law v_inst:
  for +inst: T.Instance
  for +plan: T.Plan
  for +e: {P.Plan.valid(inst, plan) == True{} : Bool}
  {P.Instance.ok(inst) == True{} : Bool}

def v_inst(inst, plan, e):
  L.and_l(P.Instance.ok(inst), Rest1(inst, plan), e)

law ok_rising:
  for +inst: T.Instance
  for +e: {P.Instance.ok(inst) == True{} : Bool}
  {J.rising(T.Instance.jobs(inst), 0n) == True{} : Bool}

def ok_rising(inst, e):
  L.and_l(J.rising(T.Instance.jobs(inst), 0n), InState(inst), e)

law ok_jobs:
  for +inst: T.Instance
  for +e: {P.Instance.ok(inst) == True{} : Bool}
  {J.in_state(T.Instance.jobs(inst), T.Instance.state(inst)) == True{} : Bool}

def ok_jobs(inst, e):
  +c = P.Crews.in_state(T.Instance.crews(inst), T.Instance.state(inst))
  L.and_l(J.in_state(T.Instance.jobs(inst), T.Instance.state(inst)), c, L.and_r(J.rising(T.Instance.jobs(inst), 0n), InState(inst), e))

law ok_crews:
  for +inst: T.Instance
  for +e: {P.Instance.ok(inst) == True{} : Bool}
  {P.Crews.in_state(T.Instance.crews(inst), T.Instance.state(inst)) == True{} : Bool}

def ok_crews(inst, e):
  +c = P.Crews.in_state(T.Instance.crews(inst), T.Instance.state(inst))
  L.and_r(J.in_state(T.Instance.jobs(inst), T.Instance.state(inst)), c, L.and_r(J.rising(T.Instance.jobs(inst), 0n), InState(inst), e))

law ok_intro:
  for +inst: T.Instance
  for +e1: {J.rising(T.Instance.jobs(inst), 0n) == True{} : Bool}
  for +e2: {J.in_state(T.Instance.jobs(inst), T.Instance.state(inst)) == True{} : Bool}
  for +e3: {P.Crews.in_state(T.Instance.crews(inst), T.Instance.state(inst)) == True{} : Bool}
  {P.Instance.ok(inst) == True{} : Bool}

def ok_intro(inst, e1, e2, e3):
  L.and_i(J.rising(T.Instance.jobs(inst), 0n), InState(inst), e1,
    L.and_i(J.in_state(T.Instance.jobs(inst), T.Instance.state(inst)), P.Crews.in_state(T.Instance.crews(inst), T.Instance.state(inst)), e2, e3))

law v_rising:
  for +inst: T.Instance
  for +plan: T.Plan
  for +e: {P.Plan.valid(inst, plan) == True{} : Bool}
  {J.rising(T.Instance.jobs(inst), 0n) == True{} : Bool}

def v_rising(inst, plan, e):
  ok_rising(inst, v_inst(inst, plan, e))

law v_rest1:
  for +inst: T.Instance
  for +plan: T.Plan
  for +e: {P.Plan.valid(inst, plan) == True{} : Bool}
  {Rest1(inst, plan) == True{} : Bool}

def v_rest1(inst, plan, e):
  L.and_r(P.Instance.ok(inst), Rest1(inst, plan), e)

law v_part:
  for +inst: T.Instance
  for +plan: T.Plan
  for +e: {P.Plan.valid(inst, plan) == True{} : Bool}
  {P.Plan.partition_ok(inst, plan) == True{} : Bool}

def v_part(inst, plan, e):
  L.and_l(P.Plan.partition_ok(inst, plan), Rest2(inst, plan), v_rest1(inst, plan, e))

law v_rest2:
  for +inst: T.Instance
  for +plan: T.Plan
  for +e: {P.Plan.valid(inst, plan) == True{} : Bool}
  {Rest2(inst, plan) == True{} : Bool}

def v_rest2(inst, plan, e):
  L.and_r(P.Plan.partition_ok(inst, plan), Rest2(inst, plan), v_rest1(inst, plan, e))

law v_slots:
  for +inst: T.Instance
  for +plan: T.Plan
  for +e: {P.Plan.valid(inst, plan) == True{} : Bool}
  {P.Slots.sorted(P.Routes.slots(T.Plan.routes(plan))) == True{} : Bool}

def v_slots(inst, plan, e):
  L.and_l(P.Slots.sorted(P.Routes.slots(T.Plan.routes(plan))), Routes3(inst, plan), v_rest2(inst, plan, e))

law v_routes:
  for +inst: T.Instance
  for +plan: T.Plan
  for +e: {P.Plan.valid(inst, plan) == True{} : Bool}
  {Routes3(inst, plan) == True{} : Bool}

def v_routes(inst, plan, e):
  L.and_r(P.Slots.sorted(P.Routes.slots(T.Plan.routes(plan))), Routes3(inst, plan), v_rest2(inst, plan, e))

law valid_intro:
  for +inst: T.Instance
  for +plan: T.Plan
  for +e1: {P.Instance.ok(inst) == True{} : Bool}
  for +e2: {P.Plan.partition_ok(inst, plan) == True{} : Bool}
  for +e3: {P.Slots.sorted(P.Routes.slots(T.Plan.routes(plan))) == True{} : Bool}
  for +e4: {Routes3(inst, plan) == True{} : Bool}
  {P.Plan.valid(inst, plan) == True{} : Bool}

def valid_intro(inst, plan, e1, e2, e3, e4):
  L.and_i(P.Instance.ok(inst), Rest1(inst, plan), e1,
    L.and_i(P.Plan.partition_ok(inst, plan), Rest2(inst, plan), e2,
      L.and_i(P.Slots.sorted(P.Routes.slots(T.Plan.routes(plan))), Routes3(inst, plan), e3, e4)))

# Counts in a valid plan match the instance's.
law count_valid:
  for +a: T.Appraisal
  for +inst: T.Instance
  for +plan: T.Plan
  for +e: {P.Plan.valid(inst, plan) == True{} : Bool}
  {J.count(a, P.Plan.placed(plan)) == J.count(a, T.Instance.jobs(inst)) : Nat}

def count_valid(a, inst, plan, e):
  PJ.count_of_same(a, P.Plan.placed(plan), T.Instance.jobs(inst), v_part(inst, plan, e))

# An edit keeps a valid plan valid
# --------------------------------

def Edit2(+inst: T.Instance, +e: H.Edit, +plan: T.Plan) -> T.Plan:
  H.Plan.edit(T.Instance.cap(inst), e, plan)

law agree_edit:
  for +zs: AL()
  for +inst: T.Instance
  for +e: H.Edit
  for +plan: T.Plan
  for +ev: {P.Plan.valid(inst, plan) == True{} : Bool}
  {PJ.agree(zs, P.Plan.placed(Edit2(inst, e, plan)), T.Instance.jobs(inst)) == True{} : Bool}

def agree_edit(zs, inst, e, plan, ev):
  match zs:
    case Nil{}:
      {==}
    case +z <> t:
      +x = P.Plan.placed(Edit2(inst, e, plan))
      +j = T.Instance.jobs(inst)
      L.and_i(Nat.is_eq(J.count(z, x), J.count(z, j)), PJ.agree(t, x, j),
        L.is_eq_of(J.count(z, x), J.count(z, j),
          Equal.trans(Nat, J.count(z, x), J.count(z, P.Plan.placed(plan)), J.count(z, j),
            count_edit(z, T.Instance.cap(inst), e, plan), count_valid(z, inst, plan, ev))),
        agree_edit(t, inst, e, plan, ev))

law valid_edit:
  for +inst: T.Instance
  for +e: H.Edit
  for +plan: T.Plan
  for +ev: {P.Plan.valid(inst, plan) == True{} : Bool}
  {P.Plan.valid(inst, Edit2(inst, e, plan)) == True{} : Bool}

def valid_edit(inst, e, plan, ev):
  +cap = T.Instance.cap(inst)
  +crews = T.Instance.crews(inst)
  +next = Edit2(inst, e, plan)
  +x = P.Plan.placed(next)
  +j = T.Instance.jobs(inst)
  +done = H.Routes.apply(T.Plan.routes(plan), cap, e)
  valid_intro(inst, next, v_inst(inst, plan, ev),
    PJ.same_sort_intro(x, j, v_rising(inst, plan, ev), agree_edit(J.sort(x), inst, e, plan, ev), agree_edit(j, inst, e, plan, ev)),
    %Equal.sym(List<&2, P.Slot>, P.Routes.slots(H.Edited.routes(done)), P.Routes.slots(T.Plan.routes(plan)), slots_apply(T.Plan.routes(plan), cap, e)) : {P.Slots.sorted(_) == True{} : Bool}
    v_slots(inst, plan, ev),
    ok_routes(T.Plan.routes(plan), crews, cap, e, v_routes(inst, plan, ev)))
