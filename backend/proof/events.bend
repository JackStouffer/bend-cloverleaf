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

# The three events that change more than a route: a cancellation, a new request
# and a backfill. Then every change at once.

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

def Crews() -> Data:
  List<&2, T.Contractor>

# Cancelling
# ----------

law ej_put:
  for +c: Bool
  for +e: T.Exception
  for +rest: XL()
  {P.Exceptions.jobs(H.Exceptions.without.put(c, e, rest)) == J.without.put(c, T.Exception.job(e), P.Exceptions.jobs(rest)) : AL()}

def ej_put(c, e, rest):
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

law ex_without:
  for +ex: XL()
  for +i: Nat
  {P.Exceptions.jobs(H.Exceptions.without(ex, i)) == J.without(P.Exceptions.jobs(ex), i) : AL()}

def ex_without(ex, i):
  match ex:
    case Nil{}:
      {==}
    case +e <> t:
      +c = Nat.is_eq(T.Appraisal.id(T.Exception.job(e)), i)
      +w = H.Exceptions.without(t, i)
      +je = T.Exception.job(e)
      Equal.trans(AL(), P.Exceptions.jobs(H.Exceptions.without.put(c, e, w)), J.without.put(c, je, P.Exceptions.jobs(w)),
        J.without.put(c, je, J.without(P.Exceptions.jobs(t), i)),
        ej_put(c, e, w),
        Equal.cong(AL(), AL(), l => J.without.put(c, je, l), P.Exceptions.jobs(w), J.without(P.Exceptions.jobs(t), i), ex_without(t, i)))

law zero_any:
  for +z: T.Appraisal
  for +xs: ST()
  for +i: Nat
  for +ez: {Nat.is_eq(T.Appraisal.id(z), i) == True{} : Bool}
  for +e: {R.Stops.any(xs, R.HasId{i}) == False{} : Bool}
  {JC(z, xs) == 0n : Nat}

def zero_any(z, xs, i, ez, e):
  match xs:
    case Nil{}:
      {==}
    case +s <> r:
      +b = Nat.is_eq(T.Stop.id(s), i)
      +rest = R.Stops.any(r, R.HasId{i})
      L.add_both_zero(J.count.one(z, T.Stop.job(s)), JC(z, r),
        PJ.one_zero.same(z, T.Stop.job(s), i, ez, L.or_l(b, rest, e)),
        zero_any(z, r, i, ez, L.or_r(b, rest, e)))

law zc:
  for +b: Bool
  for +z: T.Appraisal
  for +s: T.Stop
  for +rest: ST()
  for +i: Nat
  for +eb: {Nat.is_eq(T.Stop.id(s), i) == b : Bool}
  for +ez: {Nat.is_eq(T.Appraisal.id(z), i) == True{} : Bool}
  for +ih: {JC(z, rest) == 0n : Nat}
  {JC(z, R.Stops.put(Bool.not(b), s, rest)) == 0n : Nat}

def zc(b, z, s, rest, i, eb, ez, ih):
  match b:
    case True{}:
      ih
    case False{}:
      L.add_both_zero(J.count.one(z, T.Stop.job(s)), JC(z, rest), PJ.one_zero.same(z, T.Stop.job(s), i, ez, eb), ih)

law zero_cut:
  for +z: T.Appraisal
  for +xs: ST()
  for +i: Nat
  for +ez: {Nat.is_eq(T.Appraisal.id(z), i) == True{} : Bool}
  {JC(z, R.Stops.cut(xs, R.HasId{i})) == 0n : Nat}

def zero_cut(z, xs, i, ez):
  match xs:
    case Nil{}:
      {==}
    case +s <> r:
      zc(Nat.is_eq(T.Stop.id(s), i), z, s, R.Stops.cut(r, R.HasId{i}), i, {==}, ez, zero_cut(z, r, i, ez))

law zero_pull:
  for +z: T.Appraisal
  for +c: Bool
  for +cap: Nat
  for +r: T.Route
  for +i: Nat
  for +ez: {Nat.is_eq(T.Appraisal.id(z), i) == True{} : Bool}
  for +eh: {R.Stops.any(H.Route.h(r), R.HasId{i}) == False{} : Bool}
  for +ec: {R.Stops.any(H.Route.t(r), R.HasId{i}) == c : Bool}
  {JC(z, T.Route.stops(R.Step.route(H.Pull.if(c, cap, r, i)))) == 0n : Nat}

def zero_pull(z, c, cap, r, i, ez, eh, ec):
  match c:
    case True{}:
      +h = H.Route.h(r)
      +t = H.Route.t(r)
      +id = {R.HasId{i} : R.Test}
      +ct = R.Stops.cut(t, id)
      +kp = R.Stops.keep(t, id)
      +m = PH.Mk(cap, r, T.Route.closed(r), h, ct)
      +rs = H.Route.reshape(cap, r, T.Route.closed(r), h, ct, kp)
      +x = JC(z, T.Route.stops(R.Step.route(m)))
      +y = JC(z, R.Step.shed(m))
      %Equal.sym(T.Route, R.Step.route(R.Step.add(kp, m)), R.Step.route(m), PH.step_route(kp, m)) : {JC(z, T.Route.stops(_)) == 0n : Nat}
      L.add_zero_l(x, y,
        Equal.trans(Nat, Nat.add(x, y), Nat.add(JC(z, h), JC(z, ct)), 0n,
          PR.jc_remake(z, cap, T.Route.crew(r), T.Route.day(r), T.Route.closed(r), h, ct),
          L.add_both_zero(JC(z, h), JC(z, ct), zero_any(z, h, i, ez, eh), zero_cut(z, t, i, ez))))
    case False{}:
      +h = H.Route.h(r)
      +t = H.Route.t(r)
      Equal.trans(Nat, JC(z, T.Route.stops(r)), Nat.add(JC(z, h), JC(z, t)), 0n,
        Equal.sym(Nat, Nat.add(JC(z, h), JC(z, t)), JC(z, T.Route.stops(r)), PH.bag_route(z, r)),
        L.add_both_zero(JC(z, h), JC(z, t), zero_any(z, h, i, ez, eh), zero_any(z, t, i, ez, ec)))

law rc_none:
  for +z: T.Appraisal
  for +routes: RL()
  for +cap: Nat
  for +i: Nat
  for +ez: {Nat.is_eq(T.Appraisal.id(z), i) == True{} : Bool}
  for +eg: {H.Routes.locks(routes, i) == False{} : Bool}
  {RC(z, H.Edited.routes(H.Routes.apply(routes, cap, H.Pull{i}))) == 0n : Nat}

def rc_none(z, routes, cap, i, ez, eg):
  match routes:
    case Nil{}:
      {==}
    case +r <> t:
      +pull = {H.Pull{i} : H.Edit}
      +s = H.Route.apply(cap, pull, r)
      +rest = H.Routes.apply(t, cap, pull)
      +a = R.Stops.any(H.Route.h(r), R.HasId{i})
      +b = H.Routes.locks(t, i)
      %Equal.sym(RL(), H.Edited.routes(H.Edited.cons(s, rest)), R.Step.route(s) <> H.Edited.routes(rest), PP.edited_routes(s, rest)) : {RC(z, _) == 0n : Nat}
      Equal.trans(Nat, RC(z, R.Step.route(s) <> H.Edited.routes(rest)), Nat.add(JC(z, T.Route.stops(R.Step.route(s))), RC(z, H.Edited.routes(rest))), 0n,
        PP.rc_cons(z, R.Step.route(s), H.Edited.routes(rest)),
        L.add_both_zero(JC(z, T.Route.stops(R.Step.route(s))), RC(z, H.Edited.routes(rest)),
          zero_pull(z, R.Stops.any(H.Route.t(r), R.HasId{i}), cap, r, i, ez, L.or_l(a, b, eg), {==}),
          rc_none(z, t, cap, i, ez, L.or_r(a, b, eg))))

law ec_other:
  for +z: T.Appraisal
  for +ex: XL()
  for +i: Nat
  for +ez: {Nat.is_eq(T.Appraisal.id(z), i) == False{} : Bool}
  {EC(z, H.Exceptions.without(ex, i)) == EC(z, ex) : Nat}

def ec_other(z, ex, i, ez):
  +j = P.Exceptions.jobs(ex)
  Equal.trans(Nat, EC(z, H.Exceptions.without(ex, i)), J.count(z, J.without(j, i)), J.count(z, j),
    Equal.cong(AL(), Nat, l => J.count(z, l), P.Exceptions.jobs(H.Exceptions.without(ex, i)), J.without(j, i), ex_without(ex, i)),
    PJ.count_without_other(z, j, i, ez))

law ec_same:
  for +z: T.Appraisal
  for +ex: XL()
  for +i: Nat
  for +ez: {Nat.is_eq(T.Appraisal.id(z), i) == True{} : Bool}
  {EC(z, H.Exceptions.without(ex, i)) == 0n : Nat}

def ec_same(z, ex, i, ez):
  +j = P.Exceptions.jobs(ex)
  Equal.trans(Nat, EC(z, H.Exceptions.without(ex, i)), J.count(z, J.without(j, i)), 0n,
    Equal.cong(AL(), Nat, l => J.count(z, l), P.Exceptions.jobs(H.Exceptions.without(ex, i)), J.without(j, i), ex_without(ex, i)),
    PJ.count_without_same(z, j, i, ez))

law forget_other:
  for +z: T.Appraisal
  for +p: T.Plan
  for +i: Nat
  for +ez: {Nat.is_eq(T.Appraisal.id(z), i) == False{} : Bool}
  {J.count(z, P.Plan.placed(H.Plan.forget(p, i))) == J.count(z, P.Plan.placed(p)) : Nat}

def forget_other(z, p, i, ez):
  +rc = RC(z, T.Plan.routes(p))
  +b = T.Plan.backlog(p)
  +ex = T.Plan.exceptions(p)
  +f = H.Plan.forget(p, i)
  Equal.trans(Nat, J.count(z, P.Plan.placed(f)), Nat.add(rc, Nat.add(J.count(z, J.without(b, i)), EC(z, H.Exceptions.without(ex, i)))),
    J.count(z, P.Plan.placed(p)),
    PP.placed_count(z, f),
    Equal.trans(Nat, Nat.add(rc, Nat.add(J.count(z, J.without(b, i)), EC(z, H.Exceptions.without(ex, i)))),
      Nat.add(rc, Nat.add(J.count(z, b), EC(z, ex))), J.count(z, P.Plan.placed(p)),
      L.add_r(rc, Nat.add(J.count(z, J.without(b, i)), EC(z, H.Exceptions.without(ex, i))), Nat.add(J.count(z, b), EC(z, ex)),
        L.add_both(J.count(z, J.without(b, i)), J.count(z, b), EC(z, H.Exceptions.without(ex, i)), EC(z, ex),
          PJ.count_without_other(z, b, i, ez), ec_other(z, ex, i, ez))),
      Equal.sym(Nat, J.count(z, P.Plan.placed(p)), Nat.add(rc, Nat.add(J.count(z, b), EC(z, ex))), PP.placed_count(z, p))))

law forget_same:
  for +z: T.Appraisal
  for +p: T.Plan
  for +i: Nat
  for +ez: {Nat.is_eq(T.Appraisal.id(z), i) == True{} : Bool}
  {J.count(z, P.Plan.placed(H.Plan.forget(p, i))) == RC(z, T.Plan.routes(p)) : Nat}

def forget_same(z, p, i, ez):
  +rc = RC(z, T.Plan.routes(p))
  +b = T.Plan.backlog(p)
  +ex = T.Plan.exceptions(p)
  +f = H.Plan.forget(p, i)
  Equal.trans(Nat, J.count(z, P.Plan.placed(f)), Nat.add(rc, Nat.add(J.count(z, J.without(b, i)), EC(z, H.Exceptions.without(ex, i)))), rc,
    PP.placed_count(z, f),
    Equal.trans(Nat, Nat.add(rc, Nat.add(J.count(z, J.without(b, i)), EC(z, H.Exceptions.without(ex, i)))), Nat.add(rc, 0n), rc,
      L.add_r(rc, Nat.add(J.count(z, J.without(b, i)), EC(z, H.Exceptions.without(ex, i))), 0n,
        L.add_both_zero(J.count(z, J.without(b, i)), EC(z, H.Exceptions.without(ex, i)), PJ.count_without_same(z, b, i, ez), ec_same(z, ex, i, ez))),
      L.add_zero(rc)))

def Cut(+inst: T.Instance, +plan: T.Plan, +i: Nat) -> T.Plan:
  H.Plan.forget(H.Plan.edit(T.Instance.cap(inst), H.Pull{i}, plan), i)

# Nothing with this id is left anywhere in the plan.
law cancel_gone:
  for +z: T.Appraisal
  for +inst: T.Instance
  for +plan: T.Plan
  for +i: Nat
  for +ez: {Nat.is_eq(T.Appraisal.id(z), i) == True{} : Bool}
  for +eg: {H.Routes.locks(T.Plan.routes(plan), i) == False{} : Bool}
  {J.count(z, P.Plan.placed(Cut(inst, plan, i))) == 0n : Nat}

def cancel_gone(z, inst, plan, i, ez, eg):
  +p1 = H.Plan.edit(T.Instance.cap(inst), H.Pull{i}, plan)
  Equal.trans(Nat, J.count(z, P.Plan.placed(H.Plan.forget(p1, i))), RC(z, T.Plan.routes(p1)), 0n,
    forget_same(z, p1, i, ez),
    rc_none(z, T.Plan.routes(plan), T.Instance.cap(inst), i, ez, eg))

law count_cancel:
  for +z: T.Appraisal
  for +inst: T.Instance
  for +plan: T.Plan
  for +i: Nat
  for +ev: {P.Plan.valid(inst, plan) == True{} : Bool}
  for +eg: {H.Routes.locks(T.Plan.routes(plan), i) == False{} : Bool}
  {J.count(z, P.Plan.placed(Cut(inst, plan, i))) == J.count(z, J.without(T.Instance.jobs(inst), i)) : Nat}

def count_cancel(z, inst, plan, i, ev, eg):
  +jobs = T.Instance.jobs(inst)
  +p1 = H.Plan.edit(T.Instance.cap(inst), H.Pull{i}, plan)
  +x = J.count(z, P.Plan.placed(H.Plan.forget(p1, i)))
  L.cases(Nat.is_eq(T.Appraisal.id(z), i), {x == J.count(z, J.without(jobs, i)) : Nat},
    +e => Equal.trans(Nat, x, 0n, J.count(z, J.without(jobs, i)), cancel_gone(z, inst, plan, i, e, eg),
      Equal.sym(Nat, J.count(z, J.without(jobs, i)), 0n, PJ.count_without_same(z, jobs, i, e))),
    +e => Equal.trans(Nat, x, J.count(z, P.Plan.placed(p1)), J.count(z, J.without(jobs, i)), forget_other(z, p1, i, e),
      Equal.trans(Nat, J.count(z, P.Plan.placed(p1)), J.count(z, P.Plan.placed(plan)), J.count(z, J.without(jobs, i)),
        PP.count_edit(z, T.Instance.cap(inst), H.Pull{i}, plan),
        Equal.trans(Nat, J.count(z, P.Plan.placed(plan)), J.count(z, jobs), J.count(z, J.without(jobs, i)),
          PP.count_valid(z, inst, plan, ev),
          Equal.sym(Nat, J.count(z, J.without(jobs, i)), J.count(z, jobs), PJ.count_without_other(z, jobs, i, e))))))

law agree_cancel:
  for +zs: AL()
  for +inst: T.Instance
  for +plan: T.Plan
  for +i: Nat
  for +ev: {P.Plan.valid(inst, plan) == True{} : Bool}
  for +eg: {H.Routes.locks(T.Plan.routes(plan), i) == False{} : Bool}
  {PJ.agree(zs, P.Plan.placed(Cut(inst, plan, i)), J.without(T.Instance.jobs(inst), i)) == True{} : Bool}

def agree_cancel(zs, inst, plan, i, ev, eg):
  match zs:
    case Nil{}:
      {==}
    case +z <> t:
      +x = P.Plan.placed(Cut(inst, plan, i))
      +j = J.without(T.Instance.jobs(inst), i)
      L.and_i(Nat.is_eq(J.count(z, x), J.count(z, j)), PJ.agree(t, x, j),
        L.is_eq_of(J.count(z, x), J.count(z, j), count_cancel(z, inst, plan, i, ev, eg)),
        agree_cancel(t, inst, plan, i, ev, eg))

law valid_cancel:
  for +inst: T.Instance
  for +plan: T.Plan
  for +i: Nat
  for +ev: {P.Plan.valid(inst, plan) == True{} : Bool}
  for +eg: {H.Routes.locks(T.Plan.routes(plan), i) == False{} : Bool}
  {P.Plan.valid(H.Instance.without(inst, i), Cut(inst, plan, i)) == True{} : Bool}

def valid_cancel(inst, plan, i, ev, eg):
  +next = Cut(inst, plan, i)
  +i2 = H.Instance.without(inst, i)
  +x = P.Plan.placed(next)
  +j = J.without(T.Instance.jobs(inst), i)
  +pull = {H.Pull{i} : H.Edit}
  +ok = PP.v_inst(inst, plan, ev)
  +e1 = PJ.rising_without(T.Instance.jobs(inst), i, 0n, PP.ok_rising(inst, ok))
  +vv = PP.valid_edit(inst, pull, plan, ev)
  +p1 = PP.Edit2(inst, pull, plan)
  PP.valid_intro(i2, next, PP.ok_intro(i2, e1, PJ.in_state_without(T.Instance.jobs(inst), i, T.Instance.state(inst), PP.ok_jobs(inst, ok)), PP.ok_crews(inst, ok)),
    PJ.same_sort_intro(x, j, e1, agree_cancel(J.sort(x), inst, plan, i, ev, eg), agree_cancel(j, inst, plan, i, ev, eg)),
    PP.v_slots(inst, p1, vv), PP.v_routes(inst, p1, vv))

def Inst(+st: H.State) -> T.Instance:
  H.State.inst(st)

law cancel_valid:
  for +b: Bool
  for +inst: T.Instance
  for +plan: T.Plan
  for +i: Nat
  for +eb: {H.Routes.locks(T.Plan.routes(plan), i) == b : Bool}
  for +ev: {P.Plan.valid(inst, plan) == True{} : Bool}
  {P.Plan.valid(H.State.inst(H.cancel.if(b, inst, plan, i)), H.State.plan(H.cancel.if(b, inst, plan, i))) == True{} : Bool}

def cancel_valid(b, inst, plan, i, eb, ev):
  match b:
    case True{}:
      ev
    case False{}:
      valid_cancel(inst, plan, i, ev, eb)

law cancel_locked:
  for +b: Bool
  for +inst: T.Instance
  for +plan: T.Plan
  for +i: Nat
  for +ev: {P.Plan.valid(inst, plan) == True{} : Bool}
  {P.Routes.locked(T.Plan.routes(H.State.plan(H.cancel.if(b, inst, plan, i)))) == P.Routes.locked(T.Plan.routes(plan)) : List<&2, ST()>}

def cancel_locked(b, inst, plan, i, ev):
  match b:
    case True{}:
      {==}
    case False{}:
      PP.locked_routes(T.Plan.routes(plan), T.Instance.crews(inst), T.Instance.cap(inst), H.Pull{i}, PP.v_routes(inst, plan, ev), {==})

# Requesting
# ----------

law count_request:
  for +z: T.Appraisal
  for +inst: T.Instance
  for +plan: T.Plan
  for +job: T.Appraisal
  for +ev: {P.Plan.valid(inst, plan) == True{} : Bool}
  {J.count(z, P.Plan.placed(T.Plan{T.Plan.routes(plan), job <> T.Plan.backlog(plan), T.Plan.exceptions(plan)})) == J.count(z, J.insert(T.Instance.jobs(inst), job)) : Nat}

def count_request(z, inst, plan, job, ev):
  +p2 = {T.Plan{T.Plan.routes(plan), job <> T.Plan.backlog(plan), T.Plan.exceptions(plan)} : T.Plan}
  +rc = RC(z, T.Plan.routes(plan))
  +o = J.count.one(z, job)
  +cb = J.count(z, T.Plan.backlog(plan))
  +ec = EC(z, T.Plan.exceptions(plan))
  +jobs = T.Instance.jobs(inst)
  Equal.trans(Nat, J.count(z, P.Plan.placed(p2)), Nat.add(rc, Nat.add(Nat.add(o, cb), ec)), J.count(z, J.insert(jobs, job)),
    PP.placed_count(z, p2),
    Equal.trans(Nat, Nat.add(rc, Nat.add(Nat.add(o, cb), ec)), Nat.add(Nat.add(o, rc), Nat.add(cb, ec)), J.count(z, J.insert(jobs, job)),
      Equal.sym(Nat, Nat.add(Nat.add(o, rc), Nat.add(cb, ec)), Nat.add(rc, Nat.add(Nat.add(o, cb), ec)), L.fill_assoc(o, rc, cb, ec)),
      Equal.trans(Nat, Nat.add(Nat.add(o, rc), Nat.add(cb, ec)), Nat.add(o, Nat.add(rc, Nat.add(cb, ec))), J.count(z, J.insert(jobs, job)),
        L.add_assoc(o, rc, Nat.add(cb, ec)),
        Equal.trans(Nat, Nat.add(o, Nat.add(rc, Nat.add(cb, ec))), Nat.add(o, J.count(z, jobs)), J.count(z, J.insert(jobs, job)),
          L.add_r(o, Nat.add(rc, Nat.add(cb, ec)), J.count(z, jobs),
            Equal.trans(Nat, Nat.add(rc, Nat.add(cb, ec)), J.count(z, P.Plan.placed(plan)), J.count(z, jobs),
              Equal.sym(Nat, J.count(z, P.Plan.placed(plan)), Nat.add(rc, Nat.add(cb, ec)), PP.placed_count(z, plan)),
              PP.count_valid(z, inst, plan, ev))),
          Equal.sym(Nat, J.count(z, J.insert(jobs, job)), Nat.add(o, J.count(z, jobs)), PJ.count_insert(z, jobs, job))))))

law agree_request:
  for +zs: AL()
  for +inst: T.Instance
  for +plan: T.Plan
  for +job: T.Appraisal
  for +ev: {P.Plan.valid(inst, plan) == True{} : Bool}
  {PJ.agree(zs, P.Plan.placed(T.Plan{T.Plan.routes(plan), job <> T.Plan.backlog(plan), T.Plan.exceptions(plan)}), J.insert(T.Instance.jobs(inst), job)) == True{} : Bool}

def agree_request(zs, inst, plan, job, ev):
  match zs:
    case Nil{}:
      {==}
    case +z <> t:
      +x = P.Plan.placed(T.Plan{T.Plan.routes(plan), job <> T.Plan.backlog(plan), T.Plan.exceptions(plan)})
      +j = J.insert(T.Instance.jobs(inst), job)
      L.and_i(Nat.is_eq(J.count(z, x), J.count(z, j)), PJ.agree(t, x, j),
        L.is_eq_of(J.count(z, x), J.count(z, j), count_request(z, inst, plan, job, ev)),
        agree_request(t, inst, plan, job, ev))

law valid_request:
  for +inst: T.Instance
  for +plan: T.Plan
  for +job: T.Appraisal
  for +ev: {P.Plan.valid(inst, plan) == True{} : Bool}
  for +ek: {J.has_id(T.Instance.jobs(inst), T.Appraisal.id(job)) == False{} : Bool}
  for +es: {Nat.is_eq(T.Appraisal.state(job), T.Instance.state(inst)) == True{} : Bool}
  {P.Plan.valid(H.Instance.with(inst, job), T.Plan{T.Plan.routes(plan), job <> T.Plan.backlog(plan), T.Plan.exceptions(plan)}) == True{} : Bool}

def valid_request(inst, plan, job, ev, ek, es):
  +next = {T.Plan{T.Plan.routes(plan), job <> T.Plan.backlog(plan), T.Plan.exceptions(plan)} : T.Plan}
  +x = P.Plan.placed(next)
  +j = J.insert(T.Instance.jobs(inst), job)
  +ok = PP.v_inst(inst, plan, ev)
  +e1 = PJ.rising_insert(T.Instance.jobs(inst), job, 0n, PP.ok_rising(inst, ok), L.le_zero(T.Appraisal.id(job)), ek)
  PP.valid_intro(H.Instance.with(inst, job), next, PP.ok_intro(H.Instance.with(inst, job), e1, PJ.in_state_insert(T.Instance.jobs(inst), job, T.Instance.state(inst), PP.ok_jobs(inst, ok), es), PP.ok_crews(inst, ok)),
    PJ.same_sort_intro(x, j, e1, agree_request(J.sort(x), inst, plan, job, ev), agree_request(j, inst, plan, job, ev)),
    PP.v_slots(inst, plan, ev), PP.v_routes(inst, plan, ev))

law place_valid:
  for +c: Bool
  for +inst: T.Instance
  for +plan: T.Plan
  for +job: T.Appraisal
  for +ec: {Nat.is_eq(T.Appraisal.state(job), T.Instance.state(inst)) == c : Bool}
  for +ek: {J.has_id(T.Instance.jobs(inst), T.Appraisal.id(job)) == False{} : Bool}
  for +ev: {P.Plan.valid(inst, plan) == True{} : Bool}
  {P.Plan.valid(H.State.inst(H.request.place(c, inst, plan, job)), H.State.plan(H.request.place(c, inst, plan, job))) == True{} : Bool}

def place_valid(c, inst, plan, job, ec, ek, ev):
  match c:
    case True{}:
      valid_request(inst, plan, job, ev, ek, ec)
    case False{}:
      ev

law request_valid:
  for +b: Bool
  for +inst: T.Instance
  for +plan: T.Plan
  for +job: T.Appraisal
  for +eb: {J.has_id(T.Instance.jobs(inst), T.Appraisal.id(job)) == b : Bool}
  for +ev: {P.Plan.valid(inst, plan) == True{} : Bool}
  {P.Plan.valid(H.State.inst(H.request.if(b, inst, plan, job)), H.State.plan(H.request.if(b, inst, plan, job))) == True{} : Bool}

def request_valid(b, inst, plan, job, eb, ev):
  match b:
    case True{}:
      ev
    case False{}:
      place_valid(Nat.is_eq(T.Appraisal.state(job), T.Instance.state(inst)), inst, plan, job, {==}, eb, ev)

law place_locked:
  for +c: Bool
  for +inst: T.Instance
  for +plan: T.Plan
  for +job: T.Appraisal
  {P.Routes.locked(T.Plan.routes(H.State.plan(H.request.place(c, inst, plan, job)))) == P.Routes.locked(T.Plan.routes(plan)) : List<&2, ST()>}

def place_locked(c, inst, plan, job):
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

law request_other:
  for +b: Bool
  for +inst: T.Instance
  for +plan: T.Plan
  for +job: T.Appraisal
  for +other: {Nat.is_eq(T.Appraisal.state(job), T.Instance.state(inst)) == False{} : Bool}
  {H.request.if(b, inst, plan, job) == H.State{inst, plan} : H.State}

def request_other(b, inst, plan, job, other):
  match b:
    case True{}:
      {==}
    case False{}:
      %Equal.sym(Bool, Nat.is_eq(T.Appraisal.state(job), T.Instance.state(inst)), False{}, other) : {H.request.place(_, inst, plan, job) == H.State{inst, plan} : H.State}
      {==}

law request_locked:
  for +b: Bool
  for +inst: T.Instance
  for +plan: T.Plan
  for +job: T.Appraisal
  {P.Routes.locked(T.Plan.routes(H.State.plan(H.request.if(b, inst, plan, job)))) == P.Routes.locked(T.Plan.routes(plan)) : List<&2, ST()>}

def request_locked(b, inst, plan, job):
  match b:
    case True{}:
      {==}
    case False{}:
      place_locked(Nat.is_eq(T.Appraisal.state(job), T.Instance.state(inst)), inst, plan, job)

# Backfilling
# -----------

law jc_insert_at:
  for +a: T.Appraisal
  for +xs: ST()
  for +at: Nat
  for +s: T.Stop
  {JC(a, H.Stops.insert_at(xs, at, s)) == Nat.add(JC(a, [s]), JC(a, xs)) : Nat}

def jc_insert_at(a, xs, at, s):
  match xs at:
    case Nil{} _:
      Equal.sym(Nat, Nat.add(JC(a, [s]), 0n), JC(a, [s]), L.add_zero(JC(a, [s])))
    case h <> t 0n:
      PR.jc_one(a, s, h <> t)
    case h <> t 1n+p:
      L.swap_step(J.count.one(a, T.Stop.job(h)), JC(a, H.Stops.insert_at(t, p, s)), JC(a, [s]), JC(a, t), jc_insert_at(a, t, p, s))

law open_insert_at:
  for +xs: ST()
  for +at: Nat
  for +s: T.Stop
  for +ex: {R.Stops.all_open(xs) == True{} : Bool}
  for +es: {R.Stop.open(s) == True{} : Bool}
  {R.Stops.all_open(H.Stops.insert_at(xs, at, s)) == True{} : Bool}

def open_insert_at(xs, at, s, ex, es):
  match xs at:
    case Nil{} _:
      L.and_i(R.Stop.open(s), True{}, es, {==})
    case h <> t 0n:
      L.and_i(R.Stop.open(s), R.Stops.all_open(h <> t), es, ex)
    case h <> t 1n+p:
      L.and_i(R.Stop.open(h), R.Stops.all_open(H.Stops.insert_at(t, p, s)),
        L.and_l(R.Stop.open(h), R.Stops.all_open(t), ex),
        open_insert_at(t, p, s, L.and_r(R.Stop.open(h), R.Stops.all_open(t), ex), es))

def NewStop(+job: T.Appraisal) -> T.Stop:
  T.Stop{job, T.Open{}}

def Ins(+r: T.Route, +job: T.Appraisal, +at: Nat) -> ST():
  H.Stops.insert_at(H.Route.t(r), at, NewStop(job))

law open_ins:
  for +cap: Nat
  for +r: T.Route
  for +job: T.Appraisal
  for +at: Nat
  for +e: {R.Route.ok(cap, r) == True{} : Bool}
  {R.Stops.all_open(Ins(r, job, at)) == True{} : Bool}

def open_ins(cap, r, job, at, e):
  open_insert_at(H.Route.t(r), at, NewStop(job), PH.open_t(cap, r, e), {==})

law bag_put:
  for +a: T.Appraisal
  for +cap: Nat
  for +r: T.Route
  for +job: T.Appraisal
  for +at: Nat
  {PH.Bag(a, H.Route.put(cap, r, job, at)) == Nat.add(J.count.one(a, job), JC(a, T.Route.stops(r))) : Nat}

def bag_put(a, cap, r, job, at):
  +h = H.Route.h(r)
  +t = H.Route.t(r)
  +n = Ins(r, job, at)
  +o = J.count.one(a, job)
  Equal.trans(Nat, PH.Bag(a, H.Route.reshape(cap, r, T.Route.closed(r), h, n, Nil{})), Nat.add(JC(a, h), JC(a, n)),
    Nat.add(o, JC(a, T.Route.stops(r))),
    PH.jc_reshape(a, cap, r, T.Route.closed(r), h, n, Nil{}),
    Equal.trans(Nat, Nat.add(JC(a, h), JC(a, n)), Nat.add(JC(a, h), Nat.add(o, JC(a, t))), Nat.add(o, JC(a, T.Route.stops(r))),
      L.add_r(JC(a, h), JC(a, n), Nat.add(o, JC(a, t)),
        Equal.trans(Nat, JC(a, n), Nat.add(Nat.add(o, 0n), JC(a, t)), Nat.add(o, JC(a, t)),
          jc_insert_at(a, t, at, NewStop(job)),
          L.add_l(Nat.add(o, 0n), o, JC(a, t), L.add_zero(o)))),
      Equal.trans(Nat, Nat.add(JC(a, h), Nat.add(o, JC(a, t))), Nat.add(o, Nat.add(JC(a, h), JC(a, t))), Nat.add(o, JC(a, T.Route.stops(r))),
        L.add_swap(JC(a, h), o, JC(a, t)),
        L.add_r(o, Nat.add(JC(a, h), JC(a, t)), JC(a, T.Route.stops(r)), PH.bag_route(a, r)))))

law ok_put:
  for +cap: Nat
  for +r: T.Route
  for +job: T.Appraisal
  for +at: Nat
  for +e: {R.Route.ok(cap, r) == True{} : Bool}
  {R.Route.ok(cap, R.Step.route(H.Route.put(cap, r, job, at))) == True{} : Bool}

def ok_put(cap, r, job, at, e):
  PH.ok_reshape(cap, r, T.Route.closed(r), H.Route.h(r), Ins(r, job, at), Nil{}, PH.locked_h(r), open_ins(cap, r, job, at, e))

law crew_put:
  for +cap: Nat
  for +r: T.Route
  for +job: T.Appraisal
  for +at: Nat
  {T.Route.crew(R.Step.route(H.Route.put(cap, r, job, at))) == T.Route.crew(r) : T.Contractor}

def crew_put(cap, r, job, at):
  PH.crew_reshape(cap, r, T.Route.closed(r), H.Route.h(r), Ins(r, job, at), Nil{})

law day_put:
  for +cap: Nat
  for +r: T.Route
  for +job: T.Appraisal
  for +at: Nat
  {T.Route.day(R.Step.route(H.Route.put(cap, r, job, at))) == T.Route.day(r) : Nat}

def day_put(cap, r, job, at):
  PH.day_reshape(cap, r, T.Route.closed(r), H.Route.h(r), Ins(r, job, at), Nil{})

law lk_put:
  for +cap: Nat
  for +r: T.Route
  for +job: T.Appraisal
  for +at: Nat
  for +e: {R.Route.ok(cap, r) == True{} : Bool}
  {PH.Lk(H.Route.put(cap, r, job, at)) == R.Stops.locked(T.Route.stops(r)) : ST()}

def lk_put(cap, r, job, at, e):
  Equal.trans(ST(), PH.Lk(H.Route.reshape(cap, r, T.Route.closed(r), H.Route.h(r), Ins(r, job, at), Nil{})),
    H.Route.h(r), R.Stops.locked(T.Route.stops(r)),
    PH.locked_reshape(cap, r, T.Route.closed(r), H.Route.h(r), Ins(r, job, at), Nil{}, PH.locked_h(r), open_ins(cap, r, job, at, e)),
    PH.locked_is_h(cap, r, e))

def Tip(+t: RL()) -> H.Edited:
  H.Edited{t, Nil{}}

law eb_put_if:
  for +z: T.Appraisal
  for +m: Bool
  for +x: Bool
  for +r: T.Route
  for +t: RL()
  for +cap: Nat
  for +job: T.Appraisal
  for +at: Nat
  for +rest: H.Edited
  for +eo: {H.Routes.open_at.if(m, T.Route.closed(r), x) == True{} : Bool}
  for ih: {x == True{} : Bool} -> {PP.EB(z, rest) == Nat.add(J.count.one(z, job), RC(z, t)) : Nat}
  {PP.EB(z, H.Routes.put.if(m, r, t, cap, job, at, rest)) == Nat.add(J.count.one(z, job), RC(z, r <> t)) : Nat}

def eb_put_if(z, m, x, r, t, cap, job, at, rest, eo, ih):
  match m:
    case True{}:
      +o = J.count.one(z, job)
      +jr = JC(z, T.Route.stops(r))
      +rt = RC(z, t)
      +s = H.Route.put(cap, r, job, at)
      Equal.trans(Nat, PP.EB(z, H.Edited.cons(s, Tip(t))), Nat.add(PH.Bag(z, s), PP.EB(z, Tip(t))), Nat.add(o, RC(z, r <> t)),
        PP.eb_cons(z, s, Tip(t)),
        Equal.trans(Nat, Nat.add(PH.Bag(z, s), PP.EB(z, Tip(t))), Nat.add(Nat.add(o, jr), rt), Nat.add(o, RC(z, r <> t)),
          L.add_both(PH.Bag(z, s), Nat.add(o, jr), PP.EB(z, Tip(t)), rt, bag_put(z, cap, r, job, at), L.add_zero(rt)),
          Equal.trans(Nat, Nat.add(Nat.add(o, jr), rt), Nat.add(o, Nat.add(jr, rt)), Nat.add(o, RC(z, r <> t)),
            L.add_assoc(o, jr, rt),
            L.add_r(o, Nat.add(jr, rt), RC(z, r <> t), Equal.sym(Nat, RC(z, r <> t), Nat.add(jr, rt), PP.rc_cons(z, r, t))))))
    case False{}:
      +o = J.count.one(z, job)
      +jr = JC(z, T.Route.stops(r))
      +rt = RC(z, t)
      +s = {R.Step{r, Nil{}} : R.Step}
      Equal.trans(Nat, PP.EB(z, H.Edited.cons(s, rest)), Nat.add(PH.Bag(z, s), PP.EB(z, rest)), Nat.add(o, RC(z, r <> t)),
        PP.eb_cons(z, s, rest),
        Equal.trans(Nat, Nat.add(PH.Bag(z, s), PP.EB(z, rest)), Nat.add(jr, Nat.add(o, rt)), Nat.add(o, RC(z, r <> t)),
          L.add_both(PH.Bag(z, s), jr, PP.EB(z, rest), Nat.add(o, rt), PH.bag_same(z, r), ih(eo)),
          Equal.trans(Nat, Nat.add(jr, Nat.add(o, rt)), Nat.add(o, Nat.add(jr, rt)), Nat.add(o, RC(z, r <> t)),
            L.add_swap(jr, o, rt),
            L.add_r(o, Nat.add(jr, rt), RC(z, r <> t), Equal.sym(Nat, RC(z, r <> t), Nat.add(jr, rt), PP.rc_cons(z, r, t))))))

law eb_put:
  for +z: T.Appraisal
  for +routes: RL()
  for +cap: Nat
  for +c: Nat
  for +d: Nat
  for +job: T.Appraisal
  for +at: Nat
  for +eo: {H.Routes.open_at(routes, c, d) == True{} : Bool}
  {PP.EB(z, H.Routes.put(routes, cap, c, d, job, at)) == Nat.add(J.count.one(z, job), RC(z, routes)) : Nat}

def eb_put(z, routes, cap, c, d, job, at, eo):
  match routes:
    case Nil{}:
      L.never({PP.EB(z, H.Routes.put(Nil{}, cap, c, d, job, at)) == Nat.add(J.count.one(z, job), RC(z, Nil{})) : Nat}, eo)
    case +r <> +t:
      eb_put_if(z, H.Route.at(r, c, d), H.Routes.open_at(t, c, d), r, t, cap, job, at, H.Routes.put(t, cap, c, d, job, at), eo,
        +e => eb_put(z, t, cap, c, d, job, at, e))

law ok_put_if:
  for +m: Bool
  for +r: T.Route
  for +t: RL()
  for +crews: Crews()
  for +cap: Nat
  for +job: T.Appraisal
  for +at: Nat
  for +rest: H.Edited
  for +er: {P.Routes.ok(r <> t, crews, cap) == True{} : Bool}
  for +ih: {P.Routes.ok(H.Edited.routes(rest), crews, cap) == True{} : Bool}
  {P.Routes.ok(H.Edited.routes(H.Routes.put.if(m, r, t, cap, job, at, rest)), crews, cap) == True{} : Bool}

def ok_put_if(m, r, t, crews, cap, job, at, rest, er, ih):
  match m:
    case True{}:
      +hd = PP.routes_head(r, t, crews, cap, er)
      +s = H.Route.put(cap, r, job, at)
      PP.routes_cons(s, Tip(t), crews, cap,
        PP.fine_step(crews, cap, s, r, hd, crew_put(cap, r, job, at), ok_put(cap, r, job, at, PP.ok_of_fine(crews, cap, r, hd))),
        PP.routes_tail(r, t, crews, cap, er))
    case False{}:
      PP.routes_cons(R.Step{r, Nil{}}, rest, crews, cap, PP.routes_head(r, t, crews, cap, er), ih)

law ok_put_all:
  for +routes: RL()
  for +crews: Crews()
  for +cap: Nat
  for +c: Nat
  for +d: Nat
  for +job: T.Appraisal
  for +at: Nat
  for +er: {P.Routes.ok(routes, crews, cap) == True{} : Bool}
  {P.Routes.ok(H.Edited.routes(H.Routes.put(routes, cap, c, d, job, at)), crews, cap) == True{} : Bool}

def ok_put_all(routes, crews, cap, c, d, job, at, er):
  match routes:
    case Nil{}:
      {==}
    case +r <> +t:
      ok_put_if(H.Route.at(r, c, d), r, t, crews, cap, job, at, H.Routes.put(t, cap, c, d, job, at), er,
        ok_put_all(t, crews, cap, c, d, job, at, PP.routes_tail(r, t, crews, cap, er)))

law slots_put_if:
  for +m: Bool
  for +r: T.Route
  for +t: RL()
  for +cap: Nat
  for +job: T.Appraisal
  for +at: Nat
  for +rest: H.Edited
  for +ih: {P.Routes.slots(H.Edited.routes(rest)) == P.Routes.slots(t) : List<&2, P.Slot>}
  {P.Routes.slots(H.Edited.routes(H.Routes.put.if(m, r, t, cap, job, at, rest))) == P.Routes.slots(r <> t) : List<&2, P.Slot>}

def slots_put_if(m, r, t, cap, job, at, rest, ih):
  match m:
    case True{}:
      PP.slots_cons(H.Route.put(cap, r, job, at), r, Tip(t), t, crew_put(cap, r, job, at), day_put(cap, r, job, at), {==})
    case False{}:
      PP.slots_cons(R.Step{r, Nil{}}, r, rest, t, {==}, {==}, ih)

law slots_put:
  for +routes: RL()
  for +cap: Nat
  for +c: Nat
  for +d: Nat
  for +job: T.Appraisal
  for +at: Nat
  {P.Routes.slots(H.Edited.routes(H.Routes.put(routes, cap, c, d, job, at))) == P.Routes.slots(routes) : List<&2, P.Slot>}

def slots_put(routes, cap, c, d, job, at):
  match routes:
    case Nil{}:
      {==}
    case +r <> +t:
      slots_put_if(H.Route.at(r, c, d), r, t, cap, job, at, H.Routes.put(t, cap, c, d, job, at), slots_put(t, cap, c, d, job, at))

law locked_put_if:
  for +m: Bool
  for +r: T.Route
  for +t: RL()
  for +crews: Crews()
  for +cap: Nat
  for +job: T.Appraisal
  for +at: Nat
  for +rest: H.Edited
  for +er: {P.Routes.ok(r <> t, crews, cap) == True{} : Bool}
  for +ih: {P.Routes.locked(H.Edited.routes(rest)) == P.Routes.locked(t) : List<&2, ST()>}
  {P.Routes.locked(H.Edited.routes(H.Routes.put.if(m, r, t, cap, job, at, rest))) == P.Routes.locked(r <> t) : List<&2, ST()>}

def locked_put_if(m, r, t, crews, cap, job, at, rest, er, ih):
  match m:
    case True{}:
      +s = H.Route.put(cap, r, job, at)
      %Equal.sym(List<&2, ST()>, P.Routes.locked(H.Edited.routes(H.Edited.cons(s, Tip(t)))), PH.Lk(s) <> P.Routes.locked(t), PP.locked_cons(s, Tip(t))) : {_ == P.Routes.locked(r <> t) : List<&2, ST()>}
      %lk_put(cap, r, job, at, PP.ok_of_fine(crews, cap, r, PP.routes_head(r, t, crews, cap, er))) : {PH.Lk(s) <> P.Routes.locked(t) == _ <> P.Routes.locked(t) : List<&2, ST()>}
      {==}
    case False{}:
      +s = {R.Step{r, Nil{}} : R.Step}
      %Equal.sym(List<&2, ST()>, P.Routes.locked(H.Edited.routes(H.Edited.cons(s, rest))), PH.Lk(s) <> P.Routes.locked(H.Edited.routes(rest)), PP.locked_cons(s, rest)) : {_ == P.Routes.locked(r <> t) : List<&2, ST()>}
      %ih : {PH.Lk(s) <> P.Routes.locked(H.Edited.routes(rest)) == PH.Lk(s) <> _ : List<&2, ST()>}
      {==}

law locked_put_all:
  for +routes: RL()
  for +crews: Crews()
  for +cap: Nat
  for +c: Nat
  for +d: Nat
  for +job: T.Appraisal
  for +at: Nat
  for +er: {P.Routes.ok(routes, crews, cap) == True{} : Bool}
  {P.Routes.locked(H.Edited.routes(H.Routes.put(routes, cap, c, d, job, at))) == P.Routes.locked(routes) : List<&2, ST()>}

def locked_put_all(routes, crews, cap, c, d, job, at, er):
  match routes:
    case Nil{}:
      {==}
    case +r <> +t:
      locked_put_if(H.Route.at(r, c, d), r, t, crews, cap, job, at, H.Routes.put(t, cap, c, d, job, at), er,
        locked_put_all(t, crews, cap, c, d, job, at, PP.routes_tail(r, t, crews, cap, er)))

def Taken(+plan: T.Plan, +i: Nat) -> J.Taken:
  J.take(T.Plan.backlog(plan), i)

def Filled(+cap: Nat, +plan: T.Plan, +i: Nat, +job: T.Appraisal, +c: Nat, +d: Nat, +at: Nat) -> T.Plan:
  H.backfill.put(cap, plan, J.Taken.rest(Taken(plan, i)), job, c, d, at)

law count_fill:
  for +z: T.Appraisal
  for +cap: Nat
  for +plan: T.Plan
  for +i: Nat
  for +job: T.Appraisal
  for +c: Nat
  for +d: Nat
  for +at: Nat
  for +ef: {J.Taken.found(Taken(plan, i)) == Some{job} : Maybe<&2, T.Appraisal>}
  for +eo: {H.Routes.open_at(T.Plan.routes(plan), c, d) == True{} : Bool}
  {J.count(z, P.Plan.placed(Filled(cap, plan, i, job, c, d, at))) == J.count(z, P.Plan.placed(plan)) : Nat}

def count_fill(z, cap, plan, i, job, c, d, at, ef, eo):
  +routes = T.Plan.routes(plan)
  +ex = T.Plan.exceptions(plan)
  +b = T.Plan.backlog(plan)
  +rest = J.Taken.rest(Taken(plan, i))
  +done = H.Routes.put(routes, cap, c, d, job, at)
  +o = J.count.one(z, job)
  +rc = RC(z, routes)
  +cr = J.count(z, rest)
  +xc = EC(z, ex)
  Equal.trans(Nat, J.count(z, P.Plan.placed(H.Plan.with(H.Edited.routes(done), H.Edited.shed(done), rest, ex))),
    Nat.add(PP.EB(z, done), Nat.add(cr, xc)), J.count(z, P.Plan.placed(plan)),
    PP.count_with(z, H.Edited.routes(done), H.Edited.shed(done), rest, ex),
    Equal.trans(Nat, Nat.add(PP.EB(z, done), Nat.add(cr, xc)), Nat.add(Nat.add(o, rc), Nat.add(cr, xc)), J.count(z, P.Plan.placed(plan)),
      L.add_l(PP.EB(z, done), Nat.add(o, rc), Nat.add(cr, xc), eb_put(z, routes, cap, c, d, job, at, eo)),
      Equal.trans(Nat, Nat.add(Nat.add(o, rc), Nat.add(cr, xc)), Nat.add(rc, Nat.add(Nat.add(o, cr), xc)), J.count(z, P.Plan.placed(plan)),
        L.fill_assoc(o, rc, cr, xc),
        Equal.trans(Nat, Nat.add(rc, Nat.add(Nat.add(o, cr), xc)), Nat.add(rc, Nat.add(J.count(z, b), xc)), J.count(z, P.Plan.placed(plan)),
          L.add_r(rc, Nat.add(Nat.add(o, cr), xc), Nat.add(J.count(z, b), xc),
            L.add_l(Nat.add(o, cr), J.count(z, b), xc,
              Equal.sym(Nat, J.count(z, b), Nat.add(o, cr),
                %Equal.cong(Maybe<&2, T.Appraisal>, Nat, m => Nat.add(PJ.FC(z, m), cr), J.Taken.found(Taken(plan, i)), Some{job}, ef) : {J.count(z, b) == _ : Nat}
                PJ.take_count(z, b, i)))),
          Equal.sym(Nat, J.count(z, P.Plan.placed(plan)), Nat.add(rc, Nat.add(J.count(z, b), xc)), PP.placed_count(z, plan))))))

law agree_fill:
  for +zs: AL()
  for +inst: T.Instance
  for +plan: T.Plan
  for +i: Nat
  for +job: T.Appraisal
  for +c: Nat
  for +d: Nat
  for +at: Nat
  for +ef: {J.Taken.found(Taken(plan, i)) == Some{job} : Maybe<&2, T.Appraisal>}
  for +eo: {H.Routes.open_at(T.Plan.routes(plan), c, d) == True{} : Bool}
  for +ev: {P.Plan.valid(inst, plan) == True{} : Bool}
  {PJ.agree(zs, P.Plan.placed(Filled(T.Instance.cap(inst), plan, i, job, c, d, at)), T.Instance.jobs(inst)) == True{} : Bool}

def agree_fill(zs, inst, plan, i, job, c, d, at, ef, eo, ev):
  match zs:
    case Nil{}:
      {==}
    case +z <> t:
      +x = P.Plan.placed(Filled(T.Instance.cap(inst), plan, i, job, c, d, at))
      +j = T.Instance.jobs(inst)
      L.and_i(Nat.is_eq(J.count(z, x), J.count(z, j)), PJ.agree(t, x, j),
        L.is_eq_of(J.count(z, x), J.count(z, j),
          Equal.trans(Nat, J.count(z, x), J.count(z, P.Plan.placed(plan)), J.count(z, j),
            count_fill(z, T.Instance.cap(inst), plan, i, job, c, d, at, ef, eo), PP.count_valid(z, inst, plan, ev))),
        agree_fill(t, inst, plan, i, job, c, d, at, ef, eo, ev))

law valid_fill:
  for +inst: T.Instance
  for +plan: T.Plan
  for +i: Nat
  for +job: T.Appraisal
  for +c: Nat
  for +d: Nat
  for +at: Nat
  for +ef: {J.Taken.found(Taken(plan, i)) == Some{job} : Maybe<&2, T.Appraisal>}
  for +eo: {H.Routes.open_at(T.Plan.routes(plan), c, d) == True{} : Bool}
  for +ev: {P.Plan.valid(inst, plan) == True{} : Bool}
  {P.Plan.valid(inst, Filled(T.Instance.cap(inst), plan, i, job, c, d, at)) == True{} : Bool}

def valid_fill(inst, plan, i, job, c, d, at, ef, eo, ev):
  +cap = T.Instance.cap(inst)
  +crews = T.Instance.crews(inst)
  +next = Filled(cap, plan, i, job, c, d, at)
  +x = P.Plan.placed(next)
  +j = T.Instance.jobs(inst)
  +routes = T.Plan.routes(plan)
  PP.valid_intro(inst, next, PP.v_inst(inst, plan, ev),
    PJ.same_sort_intro(x, j, PP.v_rising(inst, plan, ev), agree_fill(J.sort(x), inst, plan, i, job, c, d, at, ef, eo, ev), agree_fill(j, inst, plan, i, job, c, d, at, ef, eo, ev)),
    %Equal.sym(List<&2, P.Slot>, P.Routes.slots(H.Edited.routes(H.Routes.put(routes, cap, c, d, job, at))), P.Routes.slots(routes), slots_put(routes, cap, c, d, job, at)) : {P.Slots.sorted(_) == True{} : Bool}
    PP.v_slots(inst, plan, ev),
    ok_put_all(routes, crews, cap, c, d, job, at, PP.v_routes(inst, plan, ev)))

law valid_check:
  for +o: Bool
  for +inst: T.Instance
  for +plan: T.Plan
  for +i: Nat
  for +job: T.Appraisal
  for +c: Nat
  for +d: Nat
  for +at: Nat
  for +ef: {J.Taken.found(Taken(plan, i)) == Some{job} : Maybe<&2, T.Appraisal>}
  for +eo: {H.Routes.open_at(T.Plan.routes(plan), c, d) == o : Bool}
  for +ev: {P.Plan.valid(inst, plan) == True{} : Bool}
  {P.Plan.valid(inst, H.backfill.check(o, T.Instance.cap(inst), plan, J.Taken.rest(Taken(plan, i)), job, c, d, at)) == True{} : Bool}

def valid_check(o, inst, plan, i, job, c, d, at, ef, eo, ev):
  match o:
    case True{}:
      valid_fill(inst, plan, i, job, c, d, at, ef, eo, ev)
    case False{}:
      ev

law valid_go:
  for +f: Maybe<&2, T.Appraisal>
  for +inst: T.Instance
  for +plan: T.Plan
  for +i: Nat
  for +c: Nat
  for +d: Nat
  for +at: Nat
  for +ef: {J.Taken.found(Taken(plan, i)) == f : Maybe<&2, T.Appraisal>}
  for +ev: {P.Plan.valid(inst, plan) == True{} : Bool}
  {P.Plan.valid(inst, H.backfill.go(T.Instance.cap(inst), plan, f, J.Taken.rest(Taken(plan, i)), c, d, at)) == True{} : Bool}

def valid_go(f, inst, plan, i, c, d, at, ef, ev):
  match f:
    case None{}:
      ev
    case Some{job}:
      valid_check(H.Routes.open_at(T.Plan.routes(plan), c, d), inst, plan, i, job, c, d, at, ef, {==}, ev)

law valid_backfill:
  for +inst: T.Instance
  for +plan: T.Plan
  for +i: Nat
  for +c: Nat
  for +d: Nat
  for +at: Nat
  for +ev: {P.Plan.valid(inst, plan) == True{} : Bool}
  {P.Plan.valid(inst, H.backfill(T.Instance.cap(inst), plan, i, c, d, at)) == True{} : Bool}

def valid_backfill(inst, plan, i, c, d, at, ev):
  valid_go(J.Taken.found(Taken(plan, i)), inst, plan, i, c, d, at, {==}, ev)

law locked_check:
  for +o: Bool
  for +inst: T.Instance
  for +plan: T.Plan
  for +rest: AL()
  for +job: T.Appraisal
  for +c: Nat
  for +d: Nat
  for +at: Nat
  for +ev: {P.Plan.valid(inst, plan) == True{} : Bool}
  {P.Routes.locked(T.Plan.routes(H.backfill.check(o, T.Instance.cap(inst), plan, rest, job, c, d, at))) == P.Routes.locked(T.Plan.routes(plan)) : List<&2, ST()>}

def locked_check(o, inst, plan, rest, job, c, d, at, ev):
  match o:
    case True{}:
      locked_put_all(T.Plan.routes(plan), T.Instance.crews(inst), T.Instance.cap(inst), c, d, job, at, PP.v_routes(inst, plan, ev))
    case False{}:
      {==}

law locked_go:
  for +f: Maybe<&2, T.Appraisal>
  for +inst: T.Instance
  for +plan: T.Plan
  for +rest: AL()
  for +c: Nat
  for +d: Nat
  for +at: Nat
  for +ev: {P.Plan.valid(inst, plan) == True{} : Bool}
  {P.Routes.locked(T.Plan.routes(H.backfill.go(T.Instance.cap(inst), plan, f, rest, c, d, at))) == P.Routes.locked(T.Plan.routes(plan)) : List<&2, ST()>}

def locked_go(f, inst, plan, rest, c, d, at, ev):
  match f:
    case None{}:
      {==}
    case Some{job}:
      locked_check(H.Routes.open_at(T.Plan.routes(plan), c, d), inst, plan, rest, job, c, d, at, ev)

law locked_backfill:
  for +inst: T.Instance
  for +plan: T.Plan
  for +i: Nat
  for +c: Nat
  for +d: Nat
  for +at: Nat
  for +ev: {P.Plan.valid(inst, plan) == True{} : Bool}
  {P.Routes.locked(T.Plan.routes(H.backfill(T.Instance.cap(inst), plan, i, c, d, at))) == P.Routes.locked(T.Plan.routes(plan)) : List<&2, ST()>}

def locked_backfill(inst, plan, i, c, d, at, ev):
  locked_go(J.Taken.found(Taken(plan, i)), inst, plan, J.Taken.rest(Taken(plan, i)), c, d, at, ev)

# Every change at once
# --------------------

def Good(+st: H.State) -> Bool:
  P.Plan.valid(H.State.inst(st), H.State.plan(st))

law good_edit:
  for +st: H.State
  for +e: H.Edit
  for +ev: {Good(st) == True{} : Bool}
  {Good(H.State.edit(st, e)) == True{} : Bool}

def good_edit(st, e, ev):
  PP.valid_edit(H.State.inst(st), e, H.State.plan(st), ev)

law good_change:
  for +st: H.State
  for +ev: H.Change
  for +e: {Good(st) == True{} : Bool}
  {Good(H.Heal.apply(st, ev)) == True{} : Bool}

def good_change(st, ev, e):
  match ev:
    case H.Cancel{i}:
      cancel_valid(H.Routes.locks(T.Plan.routes(H.State.plan(st)), i), H.State.inst(st), H.State.plan(st), i, {==}, e)
    case H.Request{job}:
      request_valid(J.has_id(T.Instance.jobs(H.State.inst(st)), T.Appraisal.id(job)), H.State.inst(st), H.State.plan(st), job, {==}, e)
    case H.Sick{c, d}:
      good_edit(st, H.Clear{c, d}, e)
    case H.Improve{c, d, n}:
      good_edit(st, H.Reorder{c, d, n}, e)
    case H.Release{i}:
      good_edit(st, H.Pull{i}, e)
    case H.Backfill{i, c, d, at}:
      valid_backfill(H.State.inst(st), H.State.plan(st), i, c, d, at, e)

law good_run:
  for +evs: List<&2, H.Change>
  for +st: H.State
  for +e: {Good(st) == True{} : Bool}
  {Good(H.Heal.run(evs, st)) == True{} : Bool}

def good_run(evs, st, e):
  match evs:
    case Nil{}:
      e
    case +ev <> t:
      good_run(t, H.Heal.apply(st, ev), good_change(st, ev, e))

law good_progress:
  for +st: H.State
  for +ev: H.Progress
  for +e: {Good(st) == True{} : Bool}
  {Good(H.Progress.apply(st, ev)) == True{} : Bool}

def good_progress(st, ev, e):
  match ev:
    case H.Started{i}:
      good_edit(st, H.Begin{i}, e)
    case H.Finished{i}:
      good_edit(st, H.Finish{i}, e)
    case H.Missed{i}:
      good_edit(st, H.Abandon{i}, e)

def Held(+st: H.State) -> List<&2, ST()>:
  P.Routes.locked(T.Plan.routes(H.State.plan(st)))

law held_edit:
  for +st: H.State
  for +e: H.Edit
  for +ev: {Good(st) == True{} : Bool}
  for +eh: {PH.Heals(e) == True{} : Bool}
  {Held(H.State.edit(st, e)) == Held(st) : List<&2, ST()>}

def held_edit(st, e, ev, eh):
  +inst = H.State.inst(st)
  +plan = H.State.plan(st)
  PP.locked_routes(T.Plan.routes(plan), T.Instance.crews(inst), T.Instance.cap(inst), e, PP.v_routes(inst, plan, ev), eh)

law held_change:
  for +st: H.State
  for +ev: H.Change
  for +e: {Good(st) == True{} : Bool}
  {Held(H.Heal.apply(st, ev)) == Held(st) : List<&2, ST()>}

def held_change(st, ev, e):
  match ev:
    case H.Cancel{i}:
      cancel_locked(H.Routes.locks(T.Plan.routes(H.State.plan(st)), i), H.State.inst(st), H.State.plan(st), i, e)
    case H.Request{job}:
      request_locked(J.has_id(T.Instance.jobs(H.State.inst(st)), T.Appraisal.id(job)), H.State.inst(st), H.State.plan(st), job)
    case H.Sick{c, d}:
      held_edit(st, H.Clear{c, d}, e, {==})
    case H.Improve{c, d, n}:
      held_edit(st, H.Reorder{c, d, n}, e, {==})
    case H.Release{i}:
      held_edit(st, H.Pull{i}, e, {==})
    case H.Backfill{i, c, d, at}:
      locked_backfill(H.State.inst(st), H.State.plan(st), i, c, d, at, e)

# A closed route takes nothing
# ----------------------------

law closed_check:
  for +o: Bool
  for +cap: Nat
  for +plan: T.Plan
  for +rest: AL()
  for +job: T.Appraisal
  for +c: Nat
  for +d: Nat
  for +at: Nat
  for +eo: {o == False{} : Bool}
  {H.backfill.check(o, cap, plan, rest, job, c, d, at) == plan : T.Plan}

def closed_check(o, cap, plan, rest, job, c, d, at, eo):
  match o:
    case True{}:
      L.clash(True{}, {H.backfill.put(cap, plan, rest, job, c, d, at) == plan : T.Plan}, {==}, eo)
    case False{}:
      {==}

law closed_go:
  for +f: Maybe<&2, T.Appraisal>
  for +cap: Nat
  for +plan: T.Plan
  for +rest: AL()
  for +c: Nat
  for +d: Nat
  for +at: Nat
  for +eo: {H.Routes.open_at(T.Plan.routes(plan), c, d) == False{} : Bool}
  {H.backfill.go(cap, plan, f, rest, c, d, at) == plan : T.Plan}

def closed_go(f, cap, plan, rest, c, d, at, eo):
  match f:
    case None{}:
      {==}
    case Some{job}:
      closed_check(H.Routes.open_at(T.Plan.routes(plan), c, d), cap, plan, rest, job, c, d, at, eo)

law closed_backfill:
  for +cap: Nat
  for +plan: T.Plan
  for +i: Nat
  for +c: Nat
  for +d: Nat
  for +at: Nat
  for +eo: {H.Routes.open_at(T.Plan.routes(plan), c, d) == False{} : Bool}
  {H.backfill(cap, plan, i, c, d, at) == plan : T.Plan}

def closed_backfill(cap, plan, i, c, d, at, eo):
  closed_go(J.Taken.found(Taken(plan, i)), cap, plan, J.Taken.rest(Taken(plan, i)), c, d, at, eo)
