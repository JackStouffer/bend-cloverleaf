import Base
import ./LAWS.bend as Laws
import ./core/types.bend as T
import ./core/lifecycle.bend as Life
import ./core/jobs.bend as J
import ./core/route.bend as R
import ./core/plan.bend as P
import ./core/heal.bend as H
import ./core/solve.bend as S
import ./proof/logic.bend as L
import ./proof/lifecycle.bend as PL
import ./proof/jobs.bend as PJ
import ./proof/plan.bend as PP
import ./proof/rules.bend as PR
import ./proof/events.bend as PE
import ./proof/solve.bend as PS
import ./proof/road.bend as PRo
import ./proof/nation.bend as PN
import ./core/nation.bend as N

# Proves every law in LAWS.bend. The working lemmas live in proof/, and this file
# only connects them to the claims.

def Laws.completed_is_final(a):
  PL.completed_step(a)

def Laws.cancelled_is_final(a):
  PL.cancelled_step(a)

def Laws.completed_stays_completed(acts):
  PL.completed_run(acts)

def Laws.cancelled_stays_cancelled(acts):
  PL.cancelled_run(acts)

def Laws.locked_status_refuses_cancel(s, e):
  PL.locked_cancel(s, e)

def Laws.only_underway_completes(s, a, e):
  PL.only_underway(s, a, e)

def Laws.every_appraisal_placed_once(inst, plan, a, ev, ea):
  +c = J.count(a, T.Instance.jobs(inst))
  Equal.trans(Nat, J.count(a, P.Plan.placed(plan)), c, 1n, PP.count_valid(a, inst, plan, ev),
    L.one_of(c, ea, PJ.rising_once(a, T.Instance.jobs(inst), 0n, PP.v_rising(inst, plan, ev))))

def Laws.nothing_else_placed(inst, plan, a, ev, ea):
  +c = J.count(a, T.Instance.jobs(inst))
  Equal.trans(Nat, J.count(a, P.Plan.placed(plan)), c, 0n, PP.count_valid(a, inst, plan, ev), L.zero_of(c, ea))

def Laws.route_starts_at_home(r):
  {==}

def Laws.route_ends_at_home(r):
  +home = T.Contractor.home(T.Route.crew(r))
  %PR.last_home(T.Route.stops(r), home, home) : {Some{List.last.go(&2, T.Point, R.Route.path.go(T.Route.stops(r), home), home)} == Some{_} : Maybe<&2, T.Point>}
  {==}

def Laws.no_stop_visited_twice(inst, plan, n, r, a, ev, on):
  PR.once_on_route(a, inst, plan, n, r, ev, on)

def Laws.routes_in_slot_order(inst, plan, n, m, a, b, ev, lt, ona, onb):
  PR.sorted_lt(P.Routes.slots(T.Plan.routes(plan)), n, m, P.Route.slot(a), P.Route.slot(b), PP.v_slots(inst, plan, ev), lt,
    PR.get_slot(T.Plan.routes(plan), n, a, ona), PR.get_slot(T.Plan.routes(plan), m, b, onb))

def Laws.slot_order_is_strict(s):
  PR.slot_lt_irrefl(s)

def Laws.route_crew_is_listed(inst, plan, n, r, ev, on):
  PR.crew_found(T.Instance.crews(inst), T.Route.crew(r),
    L.and_l(P.Crews.has(T.Instance.crews(inst), T.Route.crew(r)), R.Route.ok(T.Instance.times(inst), T.Instance.cap(inst), r), PR.fine_valid(inst, plan, n, r, ev, on)))

def Laws.route_stays_in_state(inst, plan, n, r, k, s, ev, on, at):
  PR.stays_in_state(inst, plan, n, r, k, s, ev, on, at)

def Laws.locked_stops_come_first(inst, plan, n, r, ev, on):
  PR.open_tail(T.Instance.times(inst), T.Instance.cap(inst), r, PR.ok_valid(inst, plan, n, r, ev, on))

def Laws.overtime_is_recorded(inst, plan, n, r, ev, on):
  +times = T.Instance.times(inst)
  Equal.cong(T.Audit, Bool, a => T.Audit.overtime(a), T.Route.audit(r), PR.Truth(times, r),
    PR.audit_true(T.Instance.times(inst), T.Instance.cap(inst), r, PR.ok_valid(inst, plan, n, r, ev, on)))

def Laws.off_day_is_recorded(inst, plan, n, r, ev, on):
  +times = T.Instance.times(inst)
  Equal.cong(T.Audit, Bool, a => T.Audit.off_day(a), T.Route.audit(r), PR.Truth(times, r),
    PR.audit_true(T.Instance.times(inst), T.Instance.cap(inst), r, PR.ok_valid(inst, plan, n, r, ev, on)))

def Laws.late_stop_is_recorded(inst, plan, n, k, r, s, ev, on, stop, late):
  +times = T.Instance.times(inst)
  %Equal.sym(T.Audit, T.Route.audit(r), PR.Truth(times, r), PR.audit_true(T.Instance.times(inst), T.Instance.cap(inst), r, PR.ok_valid(inst, plan, n, r, ev, on))) : {R.Nats.has(T.Audit.late(_), T.Stop.id(s)) == True{} : Bool}
  PR.late_listed(T.Route.stops(r), k, s, T.Route.day(r), stop, late)

def Laws.outside_stop_is_flagged(inst, plan, n, k, r, s, ev, on, stop, out):
  +times = T.Instance.times(inst)
  %Equal.sym(T.Audit, T.Route.audit(r), PR.Truth(times, r), PR.audit_true(T.Instance.times(inst), T.Instance.cap(inst), r, PR.ok_valid(inst, plan, n, r, ev, on))) : {R.Nats.has(T.Audit.outside(_), T.Stop.id(s)) == True{} : Bool}
  PR.outside_listed(T.Route.stops(r), k, s, T.Contractor.zips(T.Route.crew(r)), stop, out)

def Laws.outside_work_within_cap(inst, plan, n, r, ev, on):
  PR.extra_true(T.Instance.times(inst), T.Instance.cap(inst), r, PR.ok_valid(inst, plan, n, r, ev, on))

def Laws.heal_keeps_plan_valid(st, ev, e):
  PE.good_change(st, ev, e)

def Laws.heal_run_keeps_plan_valid(evs, st, e):
  PE.good_run(evs, st, e)

def Laws.progress_keeps_plan_valid(st, ev, e):
  PE.good_progress(st, ev, e)

def Laws.heal_keeps_locked_stops(st, ev, e):
  PE.held_change(st, ev, e)

def Laws.cancelled_appraisal_is_gone(inst, plan, i, z, ez, free):
  %Equal.sym(Bool, H.Routes.locks(T.Plan.routes(plan), i), False{}, free) : {J.count(z, P.Plan.placed(H.State.plan(H.cancel.if(_, inst, plan, i)))) == 0n : Nat}
  PE.cancel_gone(z, inst, plan, i, ez, free)

def Laws.locked_stop_cant_be_cancelled(inst, plan, i, held):
  %Equal.sym(Bool, H.Routes.locks(T.Plan.routes(plan), i), True{}, held) : {H.cancel.if(_, inst, plan, i) == H.State{inst, plan} : H.State}
  {==}

def Laws.repeat_request_changes_nothing(inst, plan, job, known):
  %Equal.sym(Bool, J.has_id(T.Instance.jobs(inst), T.Appraisal.id(job)), True{}, known) : {H.request.if(_, inst, plan, job) == H.State{inst, plan} : H.State}
  {==}

def Laws.request_from_another_state_changes_nothing(inst, plan, job, other):
  PE.request_other(J.has_id(T.Instance.jobs(inst), T.Appraisal.id(job)), inst, plan, job, other)

def Laws.closed_route_takes_no_new_work(times, cap, plan, i, c, d, at, closed):
  PE.closed_backfill(times, cap, plan, i, c, d, at, closed)

def Laws.trivial_plan_is_valid(inst, e):
  PS.trivial_valid(inst, e)

def Laws.published_plan_is_valid(inst, plan, e):
  PS.publish_valid(inst, plan, e)

def Laws.solved_plan_is_valid(tune, inst, first, last, e):
  PS.publish_valid(inst, S.improve(S.Tuning.passes(tune), inst, S.plan(tune, inst, first, last)), e)

def Laws.candidate_route_is_open(times, cap, job, outside, r, c, e):
  PS.fits_open(times, r, job, PS.one_fits(times, cap, job, outside, r, R.Nats.has(T.Contractor.zips(T.Route.crew(r)), T.Appraisal.zip(job)), c, e))

def Laws.candidate_meets_deadline(times, cap, job, outside, r, c, e):
  PS.fits_due(times, r, job, PS.one_fits(times, cap, job, outside, r, R.Nats.has(T.Contractor.zips(T.Route.crew(r)), T.Appraisal.zip(job)), c, e))

def Laws.candidate_within_hours(times, cap, job, outside, r, c, e):
  PS.fits_hours(times, r, job, PS.one_fits(times, cap, job, outside, r, R.Nats.has(T.Contractor.zips(T.Route.crew(r)), T.Appraisal.zip(job)), c, e))

def Laws.inside_search_stays_in_zip(times, cap, job, r, c, e):
  PS.in_zip(times, R.Nats.has(T.Contractor.zips(T.Route.crew(r)), T.Appraisal.zip(job)), r, job, c, e)

def Laws.only_urgent_work_leaves_zip(d, times, cap, last, w, job, later):
  PS.rescue_stays(Nat.is_lt(T.Appraisal.due(job), last), d, times, cap, w, job, later)

def Laws.optimizer_never_worsens_score(fuel, inst, plan):
  PS.improve_score(fuel, inst, plan)

def Laws.optimizer_keeps_plan_valid(fuel, inst, plan, ev):
  PS.improve_valid(fuel, inst, plan, ev)

def Laws.parallel_search_matches_sequential(t, d, times, cap, job, outside):
  PS.tree_seq(t, d, times, cap, job, outside)

def Laws.parallel_check_matches_sequential(inst, plan):
  PS.check_valid(inst, plan)

def Laws.national_matches_one_state_at_a_time(fuel, tune, xs, first, last):
  PN.national_seq(fuel, tune, xs, first, last)

def Laws.one_plan_per_state(fuel, tune, xs, first, last):
  +all = N.national(fuel, tune, xs, first, last)
  +one = N.national.seq(xs, tune, first, last)
  Equal.trans(Nat, List.length(&2, T.Plan, all), List.length(&2, T.Plan, one), List.length(&2, T.Instance, xs),
    Equal.cong(List<&2, T.Plan>, Nat, ps => List.length(&2, T.Plan, ps), all, one, PN.national_seq(fuel, tune, xs, first, last)),
    PN.seq_length(xs, tune, first, last))

def Laws.every_state_plan_is_valid(fuel, tune, xs, first, last, n, inst, plan, at, got, e):
  +all = N.national(fuel, tune, xs, first, last)
  +one = N.national.seq(xs, tune, first, last)
  +sol = S.solve(tune, inst, first, last)
  +chain = Equal.trans(PN.MP(), Some{plan}, List.get(&2, T.Plan, all, n), Some{sol},
    Equal.sym(PN.MP(), List.get(&2, T.Plan, all, n), Some{plan}, got),
    Equal.trans(PN.MP(), List.get(&2, T.Plan, all, n), List.get(&2, T.Plan, one, n), Some{sol},
      Equal.cong(List<&2, T.Plan>, PN.MP(), ps => List.get(&2, T.Plan, ps, n), all, one, PN.national_seq(fuel, tune, xs, first, last)),
      Equal.trans(PN.MP(), List.get(&2, T.Plan, one, n), PN.Plan.of(List.get(&2, T.Instance, xs, n), tune, first, last), Some{sol},
        PN.seq_get(xs, n, tune, first, last),
        Equal.cong(Maybe<&2, T.Instance>, PN.MP(), m => PN.Plan.of(m, tune, first, last), List.get(&2, T.Instance, xs, n), Some{inst}, at))))
  +eq = Equal.cong(PN.MP(), T.Plan, m => Maybe.default(&2, T.Plan, m, plan), Some{plan}, Some{sol}, chain)
  %Equal.sym(T.Plan, plan, sol, eq) : {P.Plan.valid(inst, _) == True{} : Bool}
  Laws.solved_plan_is_valid(tune, inst, first, last, e)

def Laws.reading_changes_nothing(a, i):
  PRo.read.law(a, i)

def Laws.checked_path_walks_the_graph(g, n, src, dst, path, c, e):
  PRo.walk.sound(path, g, n, src, dst, 0n, c, e)

def Laws.reported_time_walks_the_graph(g, w, fuel, n, limit, src, dst, stamp, c, e):
  PRo.told.walks(g, w, fuel, n, limit, src, dst, stamp, c, e)

def Laws.reported_time_within_limit(g, w, fuel, n, limit, src, dst, stamp, c, e):
  PRo.told.limit(g, w, fuel, n, limit, src, dst, stamp, c, e)

def Laws.search_keeps_the_graph(g, w, fuel, hf, n, cap, limit, src, stamp):
  PRo.keeps(fuel, hf, g, w, n, cap, limit, src, stamp)

def Laws.lookup_keeps_the_graph(g, w, fuel, n, limit, src, dst, stamp):
  PRo.lookup.keeps(g, w, fuel, n, limit, src, dst, stamp)

def Laws.dealing_keeps_every_job(xs):
  PRo.deal.back(xs)

def Laws.lanes_fit_the_budget(k, per, budget, e):
  PRo.budget.fits(k, per, budget, e)
