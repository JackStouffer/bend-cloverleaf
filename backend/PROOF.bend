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
import ./web/api.bend as WA
import ./proof/web.bend as PW
import ./proof/store.bend as PSt
import ./proof/auth.bend as PA
import ./proof/keys.bend as PK
import ./web/store.bend as WSt

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
  +passes = S.Tuning.passes(tune)
  PS.publish_valid(inst, S.improve(passes, inst, S.retry(tune, inst, S.improve(passes, inst, S.plan(tune, inst, first, last)), last)), e)

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

def Laws.decode_undoes_encode(s, v, e, w):
  PW.roundtrip(s, v, e, w)

def Laws.replies_fit_their_answers(as, r, e, w):
  PW.reply_fits(as, r, e, w)

def Laws.route_schemas_are_distinct(op):
  match op:
    case WA.Health{}:
      {==}
    case WA.Create{d, k, i}:
      {==}
    case WA.Fetch{f}:
      {==}
    case WA.Cancel{f}:
      {==}
    case WA.Organize{n, i, k, h}:
      {==}
    case WA.Rotate{f, k, h}:
      {==}
    case WA.Revoke{l, g}:
      {==}

def Laws.route_answers_are_free(op):
  match op:
    case WA.Health{}:
      {==}
    case WA.Create{d, k, i}:
      {==}
    case WA.Fetch{f}:
      {==}
    case WA.Cancel{f}:
      {==}
    case WA.Organize{n, i, k, h}:
      {==}
    case WA.Rotate{f, k, h}:
      {==}
    case WA.Revoke{l, g}:
      {==}

def Laws.handlers_stay_in_range(op):
  PW.reply_free(WA.Route.answers(WA.Op.route(op)), WA.Api.run(op), Laws.route_answers_are_free(op))

def Laws.encoded_numbers_fit(s, v, w):
  PW.encoded_fits(s, v, w)

def Laws.every_response_parses_back(op):
  PW.reply_body_fits(WA.Route.answers(WA.Op.route(op)), WA.Api.run(op), Laws.handlers_stay_in_range(op))

def Laws.every_handler_fits_its_route(op):
  PW.reply_fits(WA.Route.answers(WA.Op.route(op)), WA.Api.run(op), Laws.route_schemas_are_distinct(op), Laws.handlers_stay_in_range(op))

def Laws.spec_names_agree():
  {==}

def Laws.missing_value_is_refused(s, w):
  PW.missing_value_refused(s, w)

def Laws.missing_field_is_refused(n, k, f, r, w):
  PW.missing_field_refused(n, k, f, r, w)

def Laws.route_schemas_are_wellformed(op):
  match op:
    case WA.Health{}:
      {==}
    case WA.Create{d, k, i}:
      {==}
    case WA.Fetch{f}:
      {==}
    case WA.Cancel{f}:
      {==}
    case WA.Organize{n, i, k, h}:
      {==}
    case WA.Rotate{f, k, h}:
      {==}
    case WA.Revoke{l, g}:
      {==}

def Laws.error_schema_is_wellformed():
  {==}

def Laws.dispatcher_errors_decode(code):
  PW.roundtrip(WA.Schemas.error(), (code, (None{}, Unit{})), {==}, {==})

def Laws.replay_carries_on(xs, ys, s):
  PSt.replay_append(xs, ys, s)

def Laws.snapshot_then_rest_is_whole_log(es, n):
  PSt.replay_resumes(es, n, WSt.Store.empty())

def Laws.logged_change_reads_back(e):
  PSt.change_back(e)

def Laws.request_is_stored(s, r, fresh):
  PSt.request_is_stored(s, r, fresh)

def Laws.replayed_request_changes_nothing(s, r, x, known):
  PSt.request_again_changes_nothing(s, r, x, known)

def Laws.repeat_key_writes_nothing(d, r, id):
  {==}

def Laws.repeat_key_answers_200(d, r, id):
  {==}

def Laws.repeat_key_answers_the_stored_appraisal(d, r, id):
  {==}

def Laws.broken_request_writes_nothing(d, id, c, t, p):
  PSt.broken_request_changes_nothing(d, id, c, t, p)

def Laws.broken_request_answers_422(d, id, c, t, p):
  PSt.broken_request_is_refused(d, id, c, t, p)

def Laws.writes_publish_not_saved(op, c, w):
  match op:
    case WA.Health{}:
      L.never({WA.Route.writes(WA.Op.route(WA.Health{})) == True{} : Bool}, Equal.cong(Maybe<&2, WSt.Change>, Bool, m => Maybe.is_some(&2, WSt.Change, m), None{}, Some{c}, w))
    case WA.Create{d, k, i}:
      {==}
    case WA.Fetch{f}:
      L.never({WA.Route.writes(WA.Op.route(WA.Fetch{f})) == True{} : Bool}, Equal.cong(Maybe<&2, WSt.Change>, Bool, m => Maybe.is_some(&2, WSt.Change, m), None{}, Some{c}, w))
    case WA.Cancel{f}:
      {==}
    case WA.Organize{n, i, k, h}:
      {==}
    case WA.Rotate{f, k, h}:
      {==}
    case WA.Revoke{l, g}:
      {==}

def Laws.good_request_is_logged_open(d, id, p):
  PSt.good_request_is_logged(d, id, p)

def Laws.good_request_answers_201(d, id, p):
  PSt.good_request_is_created(d, id, p)

def Laws.new_appraisal_is_open(id, d):
  match d:
    case WSt.Draft{o, k, a, z, st, due}:
      {==}

def Laws.unknown_appraisal_answers_404():
  {==}

def Laws.cancelling_unknown_appraisal_answers_404():
  {==}

def Laws.cancelling_unknown_appraisal_writes_nothing():
  {==}

def Laws.reading_writes_nothing(m):
  {==}

def Laws.open_appraisal_is_cancelled(i, o, k, a, z, st, d):
  {==}

def Laws.locked_appraisal_writes_nothing(r, e):
  PSt.locked_appraisal_isnt_cancelled(r, e)

def Laws.locked_appraisal_answers_409(r, e):
  PSt.locked_appraisal_is_a_conflict(r, e)

def Laws.cancelling_twice_writes_nothing(i, o, k, a, z, st, d):
  {==}

def Laws.cancelling_twice_answers_200(i, o, k, a, z, st, d):
  {==}

def Laws.dealer_routes_pass_only_dealers(w, o, e):
  PA.dealers_pass(w, o, e)

def Laws.admin_routes_pass_only_the_admin(w, o, e):
  PA.admins_pass(w, o, e)

def Laws.no_key_is_unauthorized_for_dealers():
  {==}

def Laws.no_key_is_unauthorized_for_admins():
  {==}

def Laws.admin_key_is_forbidden_for_dealer_routes():
  {==}

def Laws.dealer_key_is_forbidden_for_admin_routes(o):
  {==}

def Laws.no_key_is_nobody(admin, gs):
  {==}

def Laws.dealer_has_a_stored_key(h, admin, gs, o, e):
  PA.known_dealer(h, admin, gs, o, e)

def Laws.no_admin_without_an_admin_key(h, gs, e):
  PA.no_admin(h, gs, e)

def Laws.new_key_signs_in(h, i, n, gs):
  PA.new_key_signs_in(h, i, n, gs)

def Laws.new_key_signs_in_beside_the_admin(h, a, i, n, gs, e):
  PA.new_key_beside_admin(h, a, i, n, gs, e)

def Laws.bad_name_writes_nothing(n, i, k, h, c, t, p):
  PA.bad_name_changes_nothing(n, i, k, h, c, t, p)

def Laws.bad_name_answers_422(n, i, k, h, c, t, p):
  PA.bad_name_is_refused(n, i, k, h, c, t, p)

def Laws.good_name_logs_only_the_hash(n, i, k, h, p):
  PA.good_name_is_logged(n, i, k, h, p)

def Laws.good_name_answers_201(n, i, k, h, p):
  PA.good_name_is_created(n, i, k, h, p)

def Laws.good_name_answers_the_key(n, i, k, h, p):
  PA.good_name_answers_the_key(n, i, k, h, p)

def Laws.owned_lookup_is_the_callers(o, i, rs, r, e):
  PA.owned_is_the_callers(o, i, rs, r, e)

def Laws.key_lookup_is_the_callers(o, k, rs, r, e):
  PA.keyed_is_the_callers(o, k, rs, r, e)

def Laws.reading_finds_only_the_callers(ps, body, s, o, seed, r, e):
  PA.fetch_is_the_callers(ps, body, s, o, seed, r, e)

def Laws.cancelling_finds_only_the_callers(ps, body, s, o, seed, r, e):
  PA.cancel_is_the_callers(ps, body, s, o, seed, r, e)

def Laws.repeat_key_finds_only_the_callers(ps, body, s, o, seed, d, r, id, e):
  PA.create_known(WA.Api.draft(o, body), o, s, d, r, id, e)

def Laws.new_request_belongs_to_the_caller(ps, body, s, o, seed, d, k, id, e):
  PA.create_is_the_callers(ps, body, s, o, seed, d, k, id, e)

def Laws.logged_request_is_the_callers(id, d):
  match d:
    case WSt.Draft{o, k, a, z, st, due}:
      {==}

def Laws.rotating_needs_the_admin():
  {==}

def Laws.revoking_needs_the_admin():
  {==}

def Laws.rotating_unknown_writes_nothing(k, h):
  {==}

def Laws.rotating_unknown_answers_404(k, h):
  {==}

def Laws.rotation_logs_only_the_hash(i, n, x, k, h):
  {==}

def Laws.rotation_answers_200(i, n, x, k, h):
  {==}

def Laws.rotation_answers_the_key(i, n, x, k, h):
  {==}

def Laws.revoking_is_logged(i, n, h, y):
  {==}

def Laws.revoking_answers_200(g, y):
  {==}

def Laws.revoking_answers_revoked(i, n, h, y):
  {==}

def Laws.revoking_inactive_writes_nothing(y):
  {==}

def Laws.revoking_again_answers_200(g):
  {==}

def Laws.revoking_unknown_answers_404():
  {==}

def Laws.rotation_finds_the_named_organization(ps, body, s, o, seed, g, k, h, e):
  PK.rotate_found_is_named(ps, body, s, o, seed, g, k, h, e)

def Laws.revoking_finds_the_named_organization(ps, body, s, o, seed, g, y, e):
  PK.revoke_found_is_named(ps, body, s, o, seed, g, y, e)

def Laws.rotated_key_signs_in(s, i, n, h, x, e):
  PK.rekey_signs_in(WSt.Store.org(i, s), s, i, n, h, x, e)

def Laws.rotated_key_signs_in_beside_the_admin(s, a, i, n, h, x, e, ne):
  PK.rekey_beside_admin(WSt.Store.org(i, s), s, a, i, n, h, x, e, ne)

def Laws.old_key_stops_working(s, i, n, h, k, admin, x, ex, ne, e):
  PK.rekey_old_key(WSt.Store.org(i, s), s, i, n, h, k, admin, x, ex, ne, e)

def Laws.revoked_key_signs_in_as_no_one(s, i, h, admin, e):
  PK.revoked_no_one(s, i, h, admin, e)

def Laws.rotation_keeps_other_keys(s, i, n, k, j, h, ne):
  PK.rekey_keeps_others(WSt.Store.org(i, s), s, i, n, k, j, h, ne)

def Laws.revoking_keeps_other_keys(s, i, j, h, ne):
  PK.revoke_keeps_others(s, i, j, h, ne)

def Laws.rotation_keeps_appraisals(s, g):
  PK.rekey_keeps_recs(WSt.Store.org(WSt.Org.id(g), s), g, s)

def Laws.revoking_keeps_appraisals(s, i):
  PK.revoke_keeps_recs(s, i)

def Laws.rotation_keeps_ids_fresh(s, g):
  PK.rekey_keeps_made(WSt.Store.org(WSt.Org.id(g), s), g, s)

def Laws.revoking_keeps_ids_fresh(s, i):
  PK.revoke_keeps_made(s, i)

def Laws.revoked_organization_stays_on_record(s, i, g, e):
  PK.revoked_on_record(s, i, g, e)
