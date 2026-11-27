import Base
import ./core/types.bend as T
import ./core/lifecycle.bend as Life
import ./core/jobs.bend as J
import ./core/route.bend as R
import ./core/plan.bend as P
import ./core/heal.bend as H
import ./core/solve.bend as S
import ./core/nation.bend as N
import ./road/spec.bend as Sp
import ./road/search.bend as RS
import ./road/path.bend as RP
import ./road/lanes.bend as RL
import ./web/json.bend as WJ
import ./web/schema.bend as WS
import ./web/api.bend as WA
import ./web/openapi.bend as WO
import ./web/store.bend as WSt

# The rules Cloverleaf has to keep, as claims over the pure core. PROOF.bend proves
# each one, and `bend PROOF.bend` fails until every claim holds.

def Valid(+inst: T.Instance, +plan: T.Plan) -> Data:
  {P.Plan.valid(inst, plan) == True{} : Bool}

# r is route number n of the plan.
def OnPlan(+plan: T.Plan, +n: Nat, +r: T.Route) -> Data:
  {List.get(&2, T.Route, T.Plan.routes(plan), n) == Some{r} : Maybe<&2, T.Route>}

# s is stop number k of the route.
def OnRoute(+r: T.Route, +k: Nat, +s: T.Stop) -> Data:
  {List.get(&2, T.Stop, T.Route.stops(r), k) == Some{s} : Maybe<&2, T.Stop>}

def Good(+st: H.State) -> Data:
  Valid(H.State.inst(st), H.State.plan(st))

def Locked(+st: H.State) -> List<&2, List<&2, T.Stop>>:
  P.Routes.locked(T.Plan.routes(H.State.plan(st)))

def Crew(+r: T.Route) -> T.Contractor:
  T.Route.crew(r)

# The appraisal lifecycle
# -----------------------

law completed_is_final:
  for +a: Life.Action
  {Life.step(T.Completed{}, a) == None{} : Maybe<&2, T.Status>}

law cancelled_is_final:
  for +a: Life.Action
  {Life.step(T.Cancelled{}, a) == None{} : Maybe<&2, T.Status>}

# Replaying any history keeps a finished appraisal finished.
law completed_stays_completed:
  for +acts: List<&2, Life.Action>
  {Life.run(acts, T.Completed{}) == T.Completed{} : T.Status}

law cancelled_stays_cancelled:
  for +acts: List<&2, Life.Action>
  {Life.run(acts, T.Cancelled{}) == T.Cancelled{} : T.Status}

law locked_status_refuses_cancel:
  for +s: T.Status
  for +e: {Life.Status.locked(s) == True{} : Bool}
  {Life.step(s, Life.Cancel{}) == None{} : Maybe<&2, T.Status>}

law only_underway_completes:
  for +s: T.Status
  for +a: Life.Action
  for +e: {Life.step(s, a) == Some{T.Completed{}} : Maybe<&2, T.Status>}
  {s == T.Underway{} : T.Status}

# Valid plans: every appraisal in exactly one place
# -------------------------------------------------

# Every appraisal in the instance is on a route, in the backlog, or in the
# exceptions queue, exactly once.
law every_appraisal_placed_once:
  for +inst: T.Instance
  for +plan: T.Plan
  for +a: T.Appraisal
  for +ev: Valid(inst, plan)
  for +ea: {J.has(a, T.Instance.jobs(inst)) == True{} : Bool}
  {J.count(a, P.Plan.placed(plan)) == 1n : Nat}

# And nothing else is anywhere in the plan.
law nothing_else_placed:
  for +inst: T.Instance
  for +plan: T.Plan
  for +a: T.Appraisal
  for +ev: Valid(inst, plan)
  for +ea: {J.has(a, T.Instance.jobs(inst)) == False{} : Bool}
  {J.count(a, P.Plan.placed(plan)) == 0n : Nat}

# Valid plans: routes
# -------------------

law route_starts_at_home:
  for +r: T.Route
  {List.head(&2, T.Point, R.Route.path(r)) == Some{T.Contractor.home(Crew(r))} : Maybe<&2, T.Point>}

law route_ends_at_home:
  for +r: T.Route
  {List.last(&2, T.Point, R.Route.path(r)) == Some{T.Contractor.home(Crew(r))} : Maybe<&2, T.Point>}

law no_stop_visited_twice:
  for +inst: T.Instance
  for +plan: T.Plan
  for +n: Nat
  for +r: T.Route
  for +a: T.Appraisal
  for +ev: Valid(inst, plan)
  for +on: OnPlan(plan, n, r)
  {Nat.is_le(J.count(a, R.Stops.jobs(T.Route.stops(r))), 1n) == True{} : Bool}

# Routes run in strict slot order, so no contractor has two routes on one day.
law routes_in_slot_order:
  for +inst: T.Instance
  for +plan: T.Plan
  for +n: Nat
  for +m: Nat
  for +a: T.Route
  for +b: T.Route
  for +ev: Valid(inst, plan)
  for +lt: {Nat.is_lt(n, m) == True{} : Bool}
  for +ona: OnPlan(plan, n, a)
  for +onb: OnPlan(plan, m, b)
  {P.Slot.lt(P.Route.slot(a), P.Route.slot(b)) == True{} : Bool}

law slot_order_is_strict:
  for +s: P.Slot
  {P.Slot.lt(s, s) == False{} : Bool}

# A route's contractor is one of the instance's contractors.
law route_crew_is_listed:
  for +inst: T.Instance
  for +plan: T.Plan
  for +n: Nat
  for +r: T.Route
  for +ev: Valid(inst, plan)
  for +on: OnPlan(plan, n, r)
  exs i: Nat
  {List.get(&2, T.Contractor, T.Instance.crews(inst), i) == Some{Crew(r)} : Maybe<&2, T.Contractor>}

# Contractors never work across a state line: every stop is in the contractor's
# state, including out-of-zip work done to save a deadline.
law route_stays_in_state:
  for +inst: T.Instance
  for +plan: T.Plan
  for +n: Nat
  for +r: T.Route
  for +k: Nat
  for +s: T.Stop
  for +ev: Valid(inst, plan)
  for +on: OnPlan(plan, n, r)
  for +at: OnRoute(r, k, s)
  {T.Appraisal.state(T.Stop.job(s)) == T.Contractor.state(Crew(r)) : Nat}

# Locked stops come first: everything after the locked head is still open.
law locked_stops_come_first:
  for +inst: T.Instance
  for +plan: T.Plan
  for +n: Nat
  for +r: T.Route
  for +ev: Valid(inst, plan)
  for +on: OnPlan(plan, n, r)
  {R.Stops.all_open(R.Stops.tail(T.Route.stops(r))) == True{} : Bool}

# Valid plans: limits are kept or the exception is on the record
# --------------------------------------------------------------

# The overtime flag is set exactly when the route runs past the contractor's hours.
law overtime_is_recorded:
  for +inst: T.Instance
  for +plan: T.Plan
  for +n: Nat
  for +r: T.Route
  for +ev: Valid(inst, plan)
  for +on: OnPlan(plan, n, r)
  {T.Audit.overtime(T.Route.audit(r)) == Nat.is_gt(R.Route.worked(T.Instance.times(inst), Crew(r), T.Route.stops(r)), T.Contractor.max_minutes(Crew(r))) : Bool}

# The off-day flag is set exactly when the contractor isn't available that day.
law off_day_is_recorded:
  for +inst: T.Instance
  for +plan: T.Plan
  for +n: Nat
  for +r: T.Route
  for +ev: Valid(inst, plan)
  for +on: OnPlan(plan, n, r)
  {T.Audit.off_day(T.Route.audit(r)) == Bool.not(R.Nats.has(T.Contractor.days(Crew(r)), T.Route.day(r))) : Bool}

law late_stop_is_recorded:
  for +inst: T.Instance
  for +plan: T.Plan
  for +n: Nat
  for +k: Nat
  for +r: T.Route
  for +s: T.Stop
  for +ev: Valid(inst, plan)
  for +on: OnPlan(plan, n, r)
  for +stop: OnRoute(r, k, s)
  for +late: {Nat.is_gt(T.Route.day(r), T.Appraisal.due(T.Stop.job(s))) == True{} : Bool}
  {R.Nats.has(T.Audit.late(T.Route.audit(r)), T.Stop.id(s)) == True{} : Bool}

# Out-of-zip work is flagged for admins.
law outside_stop_is_flagged:
  for +inst: T.Instance
  for +plan: T.Plan
  for +n: Nat
  for +k: Nat
  for +r: T.Route
  for +s: T.Stop
  for +ev: Valid(inst, plan)
  for +on: OnPlan(plan, n, r)
  for +stop: OnRoute(r, k, s)
  for +out: {R.Nats.has(T.Contractor.zips(Crew(r)), R.Stop.zip(s)) == False{} : Bool}
  {R.Nats.has(T.Audit.outside(T.Route.audit(r)), T.Stop.id(s)) == True{} : Bool}

# And what it adds to the drive stays within the cap.
law outside_work_within_cap:
  for +inst: T.Instance
  for +plan: T.Plan
  for +n: Nat
  for +r: T.Route
  for +ev: Valid(inst, plan)
  for +on: OnPlan(plan, n, r)
  {Nat.is_le(R.Route.extra(T.Instance.times(inst), Crew(r), T.Route.stops(r)), T.Instance.cap(inst)) == True{} : Bool}

# Healing
# -------

law heal_keeps_plan_valid:
  for +st: H.State
  for +ev: H.Change
  for +e: Good(st)
  Good(H.Heal.apply(st, ev))

law heal_run_keeps_plan_valid:
  for +evs: List<&2, H.Change>
  for +st: H.State
  for +e: Good(st)
  Good(H.Heal.run(evs, st))

# Work starting, finishing or failing also keeps a plan valid.
law progress_keeps_plan_valid:
  for +st: H.State
  for +ev: H.Progress
  for +e: Good(st)
  Good(H.Progress.apply(st, ev))

# On every route, the locked stops are the same stops in the same order.
law heal_keeps_locked_stops:
  for +st: H.State
  for +ev: H.Change
  for +e: Good(st)
  {Locked(H.Heal.apply(st, ev)) == Locked(st) : List<&2, List<&2, T.Stop>>}

# After a cancellation the appraisal is nowhere: not on a route, not in the
# backlog, not in the exceptions queue.
law cancelled_appraisal_is_gone:
  for +inst: T.Instance
  for +plan: T.Plan
  for +i: Nat
  for +z: T.Appraisal
  for +ez: {Nat.is_eq(T.Appraisal.id(z), i) == True{} : Bool}
  for +free: {H.Routes.locks(T.Plan.routes(plan), i) == False{} : Bool}
  {J.count(z, P.Plan.placed(H.State.plan(H.cancel(inst, plan, i)))) == 0n : Nat}

law locked_stop_cant_be_cancelled:
  for +inst: T.Instance
  for +plan: T.Plan
  for +i: Nat
  for +held: {H.Routes.locks(T.Plan.routes(plan), i) == True{} : Bool}
  {H.cancel(inst, plan, i) == H.State{inst, plan} : H.State}

# Retrying a request is safe.
law repeat_request_changes_nothing:
  for +inst: T.Instance
  for +plan: T.Plan
  for +job: T.Appraisal
  for +known: {J.has_id(T.Instance.jobs(inst), T.Appraisal.id(job)) == True{} : Bool}
  {H.request(inst, plan, job) == H.State{inst, plan} : H.State}

# A request from another state belongs to that state's instance, so this one
# changes nothing.
law request_from_another_state_changes_nothing:
  for +inst: T.Instance
  for +plan: T.Plan
  for +job: T.Appraisal
  for +other: {Nat.is_eq(T.Appraisal.state(job), T.Instance.state(inst)) == False{} : Bool}
  {H.request(inst, plan, job) == H.State{inst, plan} : H.State}

law closed_route_takes_no_new_work:
  for +times: T.Times
  for +cap: Nat
  for +plan: T.Plan
  for +i: Nat
  for +c: Nat
  for +d: Nat
  for +at: Nat
  for +closed: {H.Routes.open_at(T.Plan.routes(plan), c, d) == False{} : Bool}
  {H.backfill(times, cap, plan, i, c, d, at) == plan : T.Plan}

# Planning
# --------

law trivial_plan_is_valid:
  for +inst: T.Instance
  for +e: {P.Instance.ok(inst) == True{} : Bool}
  Valid(inst, P.Plan.trivial(inst))

# Whatever the planner made, what it publishes is valid.
law published_plan_is_valid:
  for +inst: T.Instance
  for +plan: T.Plan
  for +e: {P.Instance.ok(inst) == True{} : Bool}
  Valid(inst, S.publish(inst, plan))

law solved_plan_is_valid:
  for +tune: S.Tuning
  for +inst: T.Instance
  for +first: Nat
  for +last: Nat
  for +e: {P.Instance.ok(inst) == True{} : Bool}
  Valid(inst, S.solve(tune, inst, first, last))

# The planner only considers a route that takes new work.
law candidate_route_is_open:
  for +times: T.Times
  for +cap: Nat
  for +job: T.Appraisal
  for +outside: Bool
  for +r: T.Route
  for +c: S.Cand
  for +e: {S.Select.one(times, cap, job, outside, r) == Some{c} : Maybe<&2, S.Cand>}
  {T.Route.closed(r) == False{} : Bool}

# On or before the appraisal's deadline.
law candidate_meets_deadline:
  for +times: T.Times
  for +cap: Nat
  for +job: T.Appraisal
  for +outside: Bool
  for +r: T.Route
  for +c: S.Cand
  for +e: {S.Select.one(times, cap, job, outside, r) == Some{c} : Maybe<&2, S.Cand>}
  {Nat.is_le(T.Route.day(r), T.Appraisal.due(job)) == True{} : Bool}

# And with the hours left: the route so far, the added drive and the time on site.
law candidate_within_hours:
  for +times: T.Times
  for +cap: Nat
  for +job: T.Appraisal
  for +outside: Bool
  for +r: T.Route
  for +c: S.Cand
  for +e: {S.Select.one(times, cap, job, outside, r) == Some{c} : Maybe<&2, S.Cand>}
  {Nat.is_le(Nat.add(Nat.add(T.Audit.minutes(T.Route.audit(r)), S.Spot.added(S.Select.spot(times, r, T.Appraisal.site(job)))), T.Appraisal.minutes(job)), T.Contractor.max_minutes(Crew(r))) == True{} : Bool}

# The first search stays inside the contractor's zips.
law inside_search_stays_in_zip:
  for +times: T.Times
  for +cap: Nat
  for +job: T.Appraisal
  for +r: T.Route
  for +c: S.Cand
  for +e: {S.Select.one(times, cap, job, False{}, r) == Some{c} : Maybe<&2, S.Cand>}
  {R.Nats.has(T.Contractor.zips(Crew(r)), T.Appraisal.zip(job)) == True{} : Bool}

# A job with a deadline past the horizon can wait, so it never crosses a zip
# boundary: with no in-zip route it stays off the routes.
law only_urgent_work_leaves_zip:
  for +d: Nat
  for +times: T.Times
  for +cap: Nat
  for +last: Nat
  for +w: S.Work
  for +job: T.Appraisal
  for +later: {Nat.is_lt(T.Appraisal.due(job), last) == False{} : Bool}
  {S.Work.tree(S.place(None{}, d, times, cap, last, w, job)) == S.Work.tree(w) : S.Forest}

law optimizer_never_worsens_score:
  for +fuel: Nat
  for +inst: T.Instance
  for +plan: T.Plan
  {Nat.is_le(S.score(S.improve(fuel, inst, plan)), S.score(plan)) == True{} : Bool}

law optimizer_keeps_plan_valid:
  for +fuel: Nat
  for +inst: T.Instance
  for +plan: T.Plan
  for +ev: Valid(inst, plan)
  Valid(inst, S.improve(fuel, inst, plan))

# Forking the search doesn't change what it finds.
law parallel_search_matches_sequential:
  for +t: S.Forest
  for +d: Nat
  for +times: T.Times
  for +cap: Nat
  for +job: T.Appraisal
  for +outside: Bool
  {S.Select.tree(t, d, times, cap, job, outside) == S.Select.seq(S.Forest.routes(t), times, cap, job, outside) : Maybe<&2, S.Cand>}

law parallel_check_matches_sequential:
  for +inst: T.Instance
  for +plan: T.Plan
  {P.Plan.check(inst, plan) == P.Plan.valid(inst, plan) : Bool}

# The national solve
# ------------------

# Each state is solved on its own, so forking the states changes no plan.
law national_matches_one_state_at_a_time:
  for +fuel: Nat
  for +tune: S.Tuning
  for +xs: List<&2, T.Instance>
  for +first: Nat
  for +last: Nat
  {N.national(fuel, tune, xs, first, last) == N.national.seq(xs, tune, first, last) : List<&2, T.Plan>}

# Every state gets exactly one plan.
law one_plan_per_state:
  for +fuel: Nat
  for +tune: S.Tuning
  for +xs: List<&2, T.Instance>
  for +first: Nat
  for +last: Nat
  {List.length(&2, T.Plan, N.national(fuel, tune, xs, first, last)) == List.length(&2, T.Instance, xs) : Nat}

# And state n's plan is valid for state n's instance.
law every_state_plan_is_valid:
  for +fuel: Nat
  for +tune: S.Tuning
  for +xs: List<&2, T.Instance>
  for +first: Nat
  for +last: Nat
  for +n: Nat
  for +inst: T.Instance
  for +plan: T.Plan
  for +at: {List.get(&2, T.Instance, xs, n) == Some{inst} : Maybe<&2, T.Instance>}
  for +got: {List.get(&2, T.Plan, N.national(fuel, tune, xs, first, last), n) == Some{plan} : Maybe<&2, T.Plan>}
  for +e: {P.Instance.ok(inst) == True{} : Bool}
  Valid(inst, plan)

# Roads
# -----

# Base defines Array as a tree in plain Bend, and the runtime swaps in flat
# memory. Everything below rests on this: a read hands back the same array, and
# the word it reports is the one At says is there.
law reading_changes_nothing:
  for a: Array<U32>
  for +i: U32
  {(a, Sp.At(a, i)) == Array.get(U32, a, i) : Array<U32> & U32}

# If the check reports a cost, the path starts at src, ends at dst, every arc
# leaves the node the walk has reached, and the arcs' costs add up to that cost.
law checked_path_walks_the_graph:
  for g: Array<U32>
  for +n: U32
  for +src: U32
  for +dst: U32
  for +path: List<&2, U32>
  for +c: Nat
  for +e: {RP.Walked.cost(RP.Path.check(g, n, src, dst, path)) == Some{c} : Maybe<&2, Nat>}
  Sp.Walks(path, g, n, src, dst, 0n, c)

# Nothing about the search is proven beyond keeping the graph, and nothing has to
# be: whatever it did, a time only gets reported with a path that walks the graph
# at exactly that cost.
law reported_time_walks_the_graph:
  for g: Array<U32>
  for w: Array<U32>
  for +fuel: Nat
  for +n: U32
  for +limit: U32
  for +src: U32
  for +dst: U32
  for +stamp: U32
  for +c: Nat
  for +e: {RP.Cell.cost(RP.Cell.read(g, w, fuel, n, limit, src, dst, stamp)) == Some{c} : Maybe<&2, Nat>}
  Sp.Walks(RP.Cell.path(RP.Cell.read(g, w, fuel, n, limit, src, dst, stamp)), g, n, src, dst, 0n, c)

law reported_time_within_limit:
  for g: Array<U32>
  for w: Array<U32>
  for +fuel: Nat
  for +n: U32
  for +limit: U32
  for +src: U32
  for +dst: U32
  for +stamp: U32
  for +c: Nat
  for +e: {RP.Cell.cost(RP.Cell.read(g, w, fuel, n, limit, src, dst, stamp)) == Some{c} : Maybe<&2, Nat>}
  {Nat.is_le(c, U32.to_nat(limit)) == True{} : Bool}

# A lane threads one graph through every search and lookup, so these two make
# every time in a row a walk of the graph that was loaded.
law search_keeps_the_graph:
  for g: Array<U32>
  for w: Array<U32>
  for +fuel: Nat
  for +hf: Nat
  for +n: U32
  for +cap: U32
  for +limit: U32
  for +src: U32
  for +stamp: U32
  {g == RS.Out.graph(RS.Search.run(fuel, hf, g, w, n, cap, limit, src, stamp)) : Array<U32>}

law lookup_keeps_the_graph:
  for g: Array<U32>
  for w: Array<U32>
  for +fuel: Nat
  for +n: U32
  for +limit: U32
  for +src: U32
  for +dst: U32
  for +stamp: U32
  {g == RP.Cell.graph(RP.Cell.read(g, w, fuel, n, limit, src, dst, stamp)) : Array<U32>}

# Lanes get their sources one by one and hand back rows the same way, so a batch
# loses nothing and comes back in order however many lanes ran it.
law dealing_keeps_every_job:
  for xs: List<&2, U32>
  {xs == RL.Deal.undo(U32, RL.Deal.split(U32, xs)) : List<&2, U32>}

# Bend has no heap limit, so this is the only thing between a bad lane depth and
# a killed machine: the deepest tree the shell allows fits in the budget.
law lanes_fit_the_budget:
  for +k: Nat
  for +per: Nat
  for +budget: Nat
  for +e: {Nat.is_le(per, budget) == True{} : Bool}
  {Nat.is_le(Nat.mul(Nat.pow(2n, RL.Lanes.fit(k, per, budget)), per), budget) == True{} : Bool}

# The API contract
# ----------------

# The codecs agree: whatever a schema encodes, it decodes back to the same
# value. JSON can't hold one object with a key twice, so it holds for schemas
# whose objects name each field once, and every route's schemas do. The decoder
# refuses a number over Json.Max, as the parser and the spec do, so it also
# needs every number in the value to be in range, and every handler's are.
law decode_undoes_encode:
  for +s: WS.Schema
  for +v: WS.Value(s)
  for +e: {WS.Schema.distinct(s) == True{} : Bool}
  for +w: {WS.Schema.within(s, v) == True{} : Bool}
  {WS.decode(s, WS.encode(s, v)) == Some{v} : Maybe<&2, WS.Value(s)>}

# A reply can only be one of its answers, so its status is one the route
# declares and its body decodes under that status's schema.
law replies_fit_their_answers:
  for +as: List<&2, WA.Answer>
  for +r: WA.Reply(as)
  for +e: {WA.Answers.distinct(as) == True{} : Bool}
  for +w: {WA.Reply.within(as, r) == True{} : Bool}
  {WA.Answers.accepts(as, WA.Reply.status(as, r), WA.Reply.body(as, r)) == True{} : Bool}

law route_schemas_are_distinct:
  for +op: WA.Op
  {WA.Answers.distinct(WA.Route.answers(WA.Op.route(op))) == True{} : Bool}

# No route answers with a number at all: ids, keys, states and statuses are
# all strings. So nothing a handler sends can be out of range.
law route_answers_are_free:
  for +op: WA.Op
  {WA.Answers.free(WA.Route.answers(WA.Op.route(op))) == True{} : Bool}

# No handler replies with a number over Json.Max, the most the parser reads
# and the maximum the spec publishes.
law handlers_stay_in_range:
  for +op: WA.Op
  {WA.Reply.within(WA.Route.answers(WA.Op.route(op)), WA.Api.run(op)) == True{} : Bool}

# A value in range encodes with every number at most Json.Max.
law encoded_numbers_fit:
  for +s: WS.Schema
  for +v: WS.Value(s)
  for +w: {WS.Schema.within(s, v) == True{} : Bool}
  {WJ.Json.fits(WS.encode(s, v)) == True{} : Bool}

# So every body a handler sends is one the parser can read back.
law every_response_parses_back:
  for +op: WA.Op
  {WJ.Json.fits(WA.Reply.body(WA.Route.answers(WA.Op.route(op)), WA.Api.run(op))) == True{} : Bool}

# Every response a handler sends fits the route the spec publishes for it.
law every_handler_fits_its_route:
  for +op: WA.Op
  {WA.Answers.accepts(WA.Route.answers(WA.Op.route(op)),
    WA.Reply.status(WA.Route.answers(WA.Op.route(op)), WA.Api.run(op)),
    WA.Reply.body(WA.Route.answers(WA.Op.route(op)), WA.Api.run(op))) == True{} : Bool}

# Each component name in the spec has one definition, so a $ref always means
# the schema the route uses.
law spec_names_agree:
  {WO.Spec.agree(WO.Spec.all(WA.Api.routes(WA.Api.ops()))) == True{} : Bool}

# A value schema never accepts the JNil a missing key reads as.
law missing_value_is_refused:
  for +s: WS.Schema
  for +w: {WS.Schema.wellformed(s) == True{} : Bool}
  {WS.decode(s, WJ.JNil{}) == None{} : Maybe<&2, WS.Value(s)>}

# So an object without one of its required fields is refused.
law missing_field_is_refused:
  for +n: String
  for +k: String
  for +f: WS.Schema
  for +r: WS.Schema
  for +w: {WS.Schema.wellformed(f) == True{} : Bool}
  {WS.decode(WS.SObj{n, WS.SField{k, f, r}}, WJ.JObj{WJ.JNil{}}) == None{} : Maybe<&2, WS.Value(WS.SObj{n, WS.SField{k, f, r}})>}

# Every schema in the route table is well formed, so its required fields are
# required.
law route_schemas_are_wellformed:
  for +op: WA.Op
  {WA.Answers.wellformed(WA.Route.answers(WA.Op.route(op))) == True{} : Bool}

# The dispatcher's errors are in no route's answers, but they're published as
# the 4XX answer, so their schema is well formed too.
law error_schema_is_wellformed:
  {WS.Schema.wellformed(WA.Schemas.error()) == True{} : Bool}

# Every error body the dispatcher sends decodes under the published Error
# schema, back to the code it was sent with.
law dispatcher_errors_decode:
  for +code: String
  {WS.decode(WA.Schemas.error(), WA.Api.error.body(code)) == Some{(code, (None{}, Unit{}))} : Maybe<&2, WS.Value(WA.Schemas.error())>}

# The appraisal store
# -------------------

# The web process keeps appraisals as a log of changes and rebuilds the store
# by replaying it. A store replayed from part of the log carries on with the
# rest as if it had seen the whole log.
law replay_carries_on:
  for +xs: List<&2, WSt.Change>
  for +ys: List<&2, WSt.Change>
  for +s: WSt.Store
  {WSt.Store.replay(List.append(&2, WSt.Change, xs, ys), s) == WSt.Store.replay(ys, WSt.Store.replay(xs, s)) : WSt.Store}

# So a snapshot of the store after the log's first n changes, replayed with
# the changes after them, gives the store the whole log gives.
law snapshot_then_rest_is_whole_log:
  for +es: List<&2, WSt.Change>
  for +n: Nat
  {WSt.Store.replay(List.drop(&2, WSt.Change, es, n), WSt.Store.replay(List.take(&2, WSt.Change, es, n), WSt.Store.empty())) == WSt.Store.replay(es, WSt.Store.empty()) : WSt.Store}

# Every change the log writes reads back as the same change.
law logged_change_reads_back:
  for +e: WSt.Change
  {WSt.Change.read(WSt.Change.write(e)) == Some{e} : Maybe<&2, WSt.Change>}

# A request with a new id is stored, and can be read back by its id.
law request_is_stored:
  for +s: WSt.Store
  for +r: WSt.Rec
  for +fresh: {WSt.Store.find(WSt.Rec.id(r), WSt.Store.recs(s)) == None{} : Maybe<&2, WSt.Rec>}
  {WSt.Store.find(WSt.Rec.id(r), WSt.Store.recs(WSt.Store.apply(s, WSt.Requested{r}))) == Some{r} : Maybe<&2, WSt.Rec>}

# Replaying a request for an id that's already stored changes nothing.
law replayed_request_changes_nothing:
  for +s: WSt.Store
  for +r: WSt.Rec
  for +x: WSt.Rec
  for +known: {WSt.Store.find(WSt.Rec.id(r), WSt.Store.recs(s)) == Some{x} : Maybe<&2, WSt.Rec>}
  {WSt.Store.apply(s, WSt.Requested{r}) == s : WSt.Store}

# Appraisal requests
# ------------------

# Sending a key that's already stored writes nothing and answers 200 with the
# stored appraisal, so a dealer can retry a request safely.
law repeat_key_writes_nothing:
  for +d: WSt.Draft
  for +r: WSt.Rec
  for +id: String
  {WA.Api.change(WA.Create{d, Some{r}, id}) == None{} : Maybe<&2, WSt.Change>}

law repeat_key_answers_200:
  for +d: WSt.Draft
  for +r: WSt.Rec
  for +id: String
  {WA.Op.status(WA.Create{d, Some{r}, id}) == 200n : Nat}

law repeat_key_answers_the_stored_appraisal:
  for +d: WSt.Draft
  for +r: WSt.Rec
  for +id: String
  {WA.Reply.body(WA.Route.answers(WA.Op.route(WA.Create{d, Some{r}, id})), WA.Api.run(WA.Create{d, Some{r}, id})) == WS.encode(WSt.Schemas.appraisal(), WSt.Rec.value(r)) : WJ.Json}

# A request that breaks a rule writes nothing and answers 422.
law broken_request_writes_nothing:
  for +d: WSt.Draft
  for +id: String
  for +c: String
  for +t: String
  for +p: {WSt.Draft.problem(d) == Some{WSt.Problem{c, t}} : Maybe<&2, WSt.Problem>}
  {WA.Api.change(WA.Create{d, None{}, id}) == None{} : Maybe<&2, WSt.Change>}

law broken_request_answers_422:
  for +d: WSt.Draft
  for +id: String
  for +c: String
  for +t: String
  for +p: {WSt.Draft.problem(d) == Some{WSt.Problem{c, t}} : Maybe<&2, WSt.Problem>}
  {WA.Op.status(WA.Create{d, None{}, id}) == 422n : Nat}

# A new request that breaks no rule is logged as an open appraisal under the
# next id, and answers 201.
law good_request_is_logged_open:
  for +d: WSt.Draft
  for +id: String
  for +p: {WSt.Draft.problem(d) == None{} : Maybe<&2, WSt.Problem>}
  {WA.Api.change(WA.Create{d, None{}, id}) == Some{WSt.Requested{WSt.Rec.new(id, d)}} : Maybe<&2, WSt.Change>}

law good_request_answers_201:
  for +d: WSt.Draft
  for +id: String
  for +p: {WSt.Draft.problem(d) == None{} : Maybe<&2, WSt.Problem>}
  {WA.Op.status(WA.Create{d, None{}, id}) == 201n : Nat}

law new_appraisal_is_open:
  for +id: String
  for +d: WSt.Draft
  {WSt.Rec.status(WSt.Rec.new(id, d)) == T.Open{} : T.Status}

# A request that writes to the log is on a route that publishes the 500 the
# shell sends when the log can't be written.
law writes_publish_not_saved:
  for +op: WA.Op
  for +c: WSt.Change
  for +w: {WA.Api.change(op) == Some{c} : Maybe<&2, WSt.Change>}
  {WA.Route.writes(WA.Op.route(op)) == True{} : Bool}

# Reading and cancelling
# ----------------------

law unknown_appraisal_answers_404:
  {WA.Op.status(WA.Fetch{None{}}) == 404n : Nat}

law cancelling_unknown_appraisal_answers_404:
  {WA.Op.status(WA.Cancel{None{}}) == 404n : Nat}

law cancelling_unknown_appraisal_writes_nothing:
  {WA.Api.change(WA.Cancel{None{}}) == None{} : Maybe<&2, WSt.Change>}

# Reading never writes.
law reading_writes_nothing:
  for +m: Maybe<&2, WSt.Rec>
  {WA.Api.change(WA.Fetch{m}) == None{} : Maybe<&2, WSt.Change>}

# An open appraisal is cancelled, and the log records it.
law open_appraisal_is_cancelled:
  for +i: String
  for +o: String
  for +k: String
  for +a: String
  for +z: String
  for +st: WSt.StateTag()
  for +d: String
  {WA.Api.change(WA.Cancel{Some{WSt.Rec{i, o, k, a, z, st, d, T.Open{}}}}) == Some{WSt.Cancelled{i}} : Maybe<&2, WSt.Change>}

# An appraisal that's underway or completed can't be cancelled: nothing is
# written, and the answer is 409.
law locked_appraisal_writes_nothing:
  for +r: WSt.Rec
  for +e: {Life.Status.locked(WSt.Rec.status(r)) == True{} : Bool}
  {WA.Api.change(WA.Cancel{Some{r}}) == None{} : Maybe<&2, WSt.Change>}

law locked_appraisal_answers_409:
  for +r: WSt.Rec
  for +e: {Life.Status.locked(WSt.Rec.status(r)) == True{} : Bool}
  {WA.Op.status(WA.Cancel{Some{r}}) == 409n : Nat}

# Cancelling an appraisal that's already cancelled writes nothing and answers
# 200, so a cancel can be retried safely.
law cancelling_twice_writes_nothing:
  for +i: String
  for +o: String
  for +k: String
  for +a: String
  for +z: String
  for +st: WSt.StateTag()
  for +d: String
  {WA.Api.change(WA.Cancel{Some{WSt.Rec{i, o, k, a, z, st, d, T.Cancelled{}}}}) == None{} : Maybe<&2, WSt.Change>}

law cancelling_twice_answers_200:
  for +i: String
  for +o: String
  for +k: String
  for +a: String
  for +z: String
  for +st: WSt.StateTag()
  for +d: String
  {WA.Op.status(WA.Cancel{Some{WSt.Rec{i, o, k, a, z, st, d, T.Cancelled{}}}}) == 200n : Nat}

# API keys
# --------

# Each route says who may call it. Laws about keys speak of the hash h of the
# key a request brings, which the store compares, since it keeps no key.

# A dealer route lets a caller through only as the dealer organization the
# caller's key belongs to.
law dealer_routes_pass_only_dealers:
  for +w: WA.Who
  for +o: String
  for +e: {WA.Api.gate(WA.Dealers{}, w) == WA.Pass{o} : WA.Gate}
  {w == WA.Dealer{o} : WA.Who}

# An admin route lets only the admin through.
law admin_routes_pass_only_the_admin:
  for +w: WA.Who
  for +o: String
  for +e: {WA.Api.gate(WA.Admins{}, w) == WA.Pass{o} : WA.Gate}
  {w == WA.Admin{} : WA.Who}

# A request with no key, or a key nobody has, is refused with a 401 by any
# route that needs a key.
law no_key_is_unauthorized_for_dealers:
  {WA.Api.gate(WA.Dealers{}, WA.Nobody{}) == WA.Deny{WA.Unauthorized{}, "unauthorized"} : WA.Gate}

law no_key_is_unauthorized_for_admins:
  {WA.Api.gate(WA.Admins{}, WA.Nobody{}) == WA.Deny{WA.Unauthorized{}, "unauthorized"} : WA.Gate}

# A key for the other kind of route is refused with a 403.
law admin_key_is_forbidden_for_dealer_routes:
  {WA.Api.gate(WA.Dealers{}, WA.Admin{}) == WA.Deny{WA.Forbidden{}, "forbidden"} : WA.Gate}

law dealer_key_is_forbidden_for_admin_routes:
  for +o: String
  {WA.Api.gate(WA.Admins{}, WA.Dealer{o}) == WA.Deny{WA.Forbidden{}, "forbidden"} : WA.Gate}

law no_key_is_nobody:
  for +admin: Maybe<&2, String>
  for +gs: List<&2, WSt.Org>
  {WA.Api.who(None{}, admin, gs) == WA.Nobody{} : WA.Who}

# A key makes its caller a dealer only when the store holds an organization
# with that id and that key's hash.
law dealer_has_a_stored_key:
  for +h: String
  for +admin: Maybe<&2, String>
  for +gs: List<&2, WSt.Org>
  for +o: String
  for +e: {WA.Api.known(h, admin, gs) == WA.Dealer{o} : WA.Who}
  {WSt.Orgs.holds(o, h, gs) == True{} : Bool}

# Without an admin key in the environment, nobody is the admin.
law no_admin_without_an_admin_key:
  for +h: String
  for +gs: List<&2, WSt.Org>
  for e: {WA.Api.known(h, None{}, gs) == WA.Admin{} : WA.Who}
  Empty

# A new organization's key, once the organization is stored, signs in as
# that organization, unless it's the admin key.
law new_key_signs_in:
  for +h: String
  for +i: String
  for +n: String
  for +gs: List<&2, WSt.Org>
  {WA.Api.known(h, None{}, WSt.Org{i, n, h} <> gs) == WA.Dealer{i} : WA.Who}

law new_key_signs_in_beside_the_admin:
  for +h: String
  for +a: String
  for +i: String
  for +n: String
  for +gs: List<&2, WSt.Org>
  for +e: {WJ.Text.same(h, a) == False{} : Bool}
  {WA.Api.known(h, Some{a}, WSt.Org{i, n, h} <> gs) == WA.Dealer{i} : WA.Who}

# Adding organizations
# --------------------

# A name that breaks a rule writes nothing and answers 422.
law bad_name_writes_nothing:
  for +n: String
  for +i: String
  for +k: String
  for +h: String
  for +c: String
  for +t: String
  for +p: {WSt.Org.problem(n) == Some{WSt.Problem{c, t}} : Maybe<&2, WSt.Problem>}
  {WA.Api.change(WA.Organize{n, i, k, h}) == None{} : Maybe<&2, WSt.Change>}

law bad_name_answers_422:
  for +n: String
  for +i: String
  for +k: String
  for +h: String
  for +c: String
  for +t: String
  for +p: {WSt.Org.problem(n) == Some{WSt.Problem{c, t}} : Maybe<&2, WSt.Problem>}
  {WA.Op.status(WA.Organize{n, i, k, h}) == 422n : Nat}

# A good name is logged with the key's hash and never the key, and answers
# 201 with the key, the one time it's shown.
law good_name_logs_only_the_hash:
  for +n: String
  for +i: String
  for +k: String
  for +h: String
  for +p: {WSt.Org.problem(n) == None{} : Maybe<&2, WSt.Problem>}
  {WA.Api.change(WA.Organize{n, i, k, h}) == Some{WSt.Organized{WSt.Org{i, n, h}}} : Maybe<&2, WSt.Change>}

law good_name_answers_201:
  for +n: String
  for +i: String
  for +k: String
  for +h: String
  for +p: {WSt.Org.problem(n) == None{} : Maybe<&2, WSt.Problem>}
  {WA.Op.status(WA.Organize{n, i, k, h}) == 201n : Nat}

law good_name_answers_the_key:
  for +n: String
  for +i: String
  for +k: String
  for +h: String
  for +p: {WSt.Org.problem(n) == None{} : Maybe<&2, WSt.Problem>}
  {WA.Reply.body(WA.Route.answers(WA.Op.route(WA.Organize{n, i, k, h})), WA.Api.run(WA.Organize{n, i, k, h})) == WS.encode(WSt.Schemas.org.key(), (i, (n, (k, Unit{})))) : WJ.Json}

# Tenant isolation
# ----------------

# A dealer's lookups only find records its own organization owns, so another
# dealer's appraisal reads as missing.
law owned_lookup_is_the_callers:
  for +o: String
  for +i: String
  for +rs: List<&2, WSt.Rec>
  for +r: WSt.Rec
  for +e: {WSt.Store.owned(o, i, rs) == Some{r} : Maybe<&2, WSt.Rec>}
  {WJ.Text.same(o, WSt.Rec.org(r)) == True{} : Bool}

law key_lookup_is_the_callers:
  for +o: String
  for +k: String
  for +rs: List<&2, WSt.Rec>
  for +r: WSt.Rec
  for +e: {WSt.Store.by_key(o, k, rs) == Some{r} : Maybe<&2, WSt.Rec>}
  {WJ.Text.same(o, WSt.Rec.org(r)) == True{} : Bool}

# So a request the gate passed as organization o reads, cancels and repeats
# only o's appraisals, and a new one belongs to o, whatever its body says.
law reading_finds_only_the_callers:
  for +ps: List<&2, String>
  for +body: String
  for +s: WSt.Store
  for +o: String
  for +seed: List<&2, U32>
  for +r: WSt.Rec
  for +e: {WA.Api.resolve(WA.EFetch{}, ps, body, s, o, seed) == WA.Handle{WA.Fetch{Some{r}}} : WA.Resolved}
  {WJ.Text.same(o, WSt.Rec.org(r)) == True{} : Bool}

law cancelling_finds_only_the_callers:
  for +ps: List<&2, String>
  for +body: String
  for +s: WSt.Store
  for +o: String
  for +seed: List<&2, U32>
  for +r: WSt.Rec
  for +e: {WA.Api.resolve(WA.ECancel{}, ps, body, s, o, seed) == WA.Handle{WA.Cancel{Some{r}}} : WA.Resolved}
  {WJ.Text.same(o, WSt.Rec.org(r)) == True{} : Bool}

law repeat_key_finds_only_the_callers:
  for +ps: List<&2, String>
  for +body: String
  for +s: WSt.Store
  for +o: String
  for +seed: List<&2, U32>
  for +d: WSt.Draft
  for +r: WSt.Rec
  for +id: String
  for +e: {WA.Api.resolve(WA.ECreate{}, ps, body, s, o, seed) == WA.Handle{WA.Create{d, Some{r}, id}} : WA.Resolved}
  {WJ.Text.same(o, WSt.Rec.org(r)) == True{} : Bool}

law new_request_belongs_to_the_caller:
  for +ps: List<&2, String>
  for +body: String
  for +s: WSt.Store
  for +o: String
  for +seed: List<&2, U32>
  for +d: WSt.Draft
  for +k: Maybe<&2, WSt.Rec>
  for +id: String
  for +e: {WA.Api.resolve(WA.ECreate{}, ps, body, s, o, seed) == WA.Handle{WA.Create{d, k, id}} : WA.Resolved}
  {WSt.Draft.org(d) == o : String}

# And the record a new request logs is the caller's.
law logged_request_is_the_callers:
  for +id: String
  for +d: WSt.Draft
  {WSt.Rec.org(WSt.Rec.new(id, d)) == WSt.Draft.org(d) : String}
