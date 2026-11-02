import Base
import ./core/types.bend as T
import ./core/lifecycle.bend as Life
import ./core/jobs.bend as J
import ./core/route.bend as R
import ./core/plan.bend as P
import ./core/heal.bend as H
import ./core/solve.bend as S
import ./road/spec.bend as Sp
import ./road/search.bend as RS
import ./road/path.bend as RP
import ./road/lanes.bend as RL

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
  {T.Audit.overtime(T.Route.audit(r)) == Nat.is_gt(R.Route.worked(Crew(r), T.Route.stops(r)), T.Contractor.max_minutes(Crew(r))) : Bool}

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
  {Nat.is_le(R.Route.extra(Crew(r), T.Route.stops(r)), T.Instance.cap(inst)) == True{} : Bool}

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
  for +cap: Nat
  for +plan: T.Plan
  for +i: Nat
  for +c: Nat
  for +d: Nat
  for +at: Nat
  for +closed: {H.Routes.open_at(T.Plan.routes(plan), c, d) == False{} : Bool}
  {H.backfill(cap, plan, i, c, d, at) == plan : T.Plan}

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
  for +cap: Nat
  for +job: T.Appraisal
  for +outside: Bool
  for +r: T.Route
  for +c: S.Cand
  for +e: {S.Select.one(cap, job, outside, r) == Some{c} : Maybe<&2, S.Cand>}
  {T.Route.closed(r) == False{} : Bool}

# On or before the appraisal's deadline.
law candidate_meets_deadline:
  for +cap: Nat
  for +job: T.Appraisal
  for +outside: Bool
  for +r: T.Route
  for +c: S.Cand
  for +e: {S.Select.one(cap, job, outside, r) == Some{c} : Maybe<&2, S.Cand>}
  {Nat.is_le(T.Route.day(r), T.Appraisal.due(job)) == True{} : Bool}

# And with the hours left: the route so far, the added drive and the time on site.
law candidate_within_hours:
  for +cap: Nat
  for +job: T.Appraisal
  for +outside: Bool
  for +r: T.Route
  for +c: S.Cand
  for +e: {S.Select.one(cap, job, outside, r) == Some{c} : Maybe<&2, S.Cand>}
  {Nat.is_le(Nat.add(Nat.add(T.Audit.minutes(T.Route.audit(r)), S.Spot.added(S.Select.spot(r, T.Appraisal.site(job)))), T.Appraisal.minutes(job)), T.Contractor.max_minutes(Crew(r))) == True{} : Bool}

# The first search stays inside the contractor's zips.
law inside_search_stays_in_zip:
  for +cap: Nat
  for +job: T.Appraisal
  for +r: T.Route
  for +c: S.Cand
  for +e: {S.Select.one(cap, job, False{}, r) == Some{c} : Maybe<&2, S.Cand>}
  {R.Nats.has(T.Contractor.zips(Crew(r)), T.Appraisal.zip(job)) == True{} : Bool}

# A job with a deadline past the horizon can wait, so it never crosses a zip
# boundary: with no in-zip route it stays off the routes.
law only_urgent_work_leaves_zip:
  for +d: Nat
  for +cap: Nat
  for +last: Nat
  for +w: S.Work
  for +job: T.Appraisal
  for +later: {Nat.is_lt(T.Appraisal.due(job), last) == False{} : Bool}
  {S.Work.tree(S.place(None{}, d, cap, last, w, job)) == S.Work.tree(w) : S.Forest}

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
  for +cap: Nat
  for +job: T.Appraisal
  for +outside: Bool
  {S.Select.tree(t, d, cap, job, outside) == S.Select.seq(S.Forest.routes(t), cap, job, outside) : Maybe<&2, S.Cand>}

law parallel_check_matches_sequential:
  for +inst: T.Instance
  for +plan: T.Plan
  {P.Plan.check(inst, plan) == P.Plan.valid(inst, plan) : Bool}

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
