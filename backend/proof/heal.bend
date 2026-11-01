import Base
import ../core/types.bend as T
import ../core/lifecycle.bend as Life
import ../core/jobs.bend as J
import ../core/route.bend as R
import ../core/plan.bend as P
import ../core/heal.bend as H
import ./logic.bend as L
import ./jobs.bend as PJ
import ./route.bend as PR

# Route edits: each one keeps a valid route valid, loses nothing, and leaves the
# crew and day alone. The three that heal also leave locked stops alone.

def ST() -> Data:
  List<&2, T.Stop>

def JC(+a: T.Appraisal, xs: List<&2, T.Stop>) -> Nat:
  J.count(a, R.Stops.jobs(xs))

def Mk(+cap: Nat, +r: T.Route, +k: Bool, +h: ST(), +t: ST()) -> R.Step:
  R.Route.remake(cap, T.Route.crew(r), T.Route.day(r), k, h, t)

law step_route:
  for +out: ST()
  for +m: R.Step
  {R.Step.route(R.Step.add(out, m)) == R.Step.route(m) : T.Route}

def step_route(out, m):
  match m:
    case R.Step{r, x}:
      {==}

law step_shed:
  for +out: ST()
  for +m: R.Step
  {R.Step.shed(R.Step.add(out, m)) == R.Stops.append(out, R.Step.shed(m)) : ST()}

def step_shed(out, m):
  match m:
    case R.Step{r, x}:
      {==}

# Reshape inherits everything from remake
# ---------------------------------------

law ok_reshape:
  for +cap: Nat
  for +r: T.Route
  for +k: Bool
  for +h: ST()
  for +t: ST()
  for +out: ST()
  for +eh: {R.Stops.all_locked(h) == True{} : Bool}
  for +et: {R.Stops.all_open(t) == True{} : Bool}
  {R.Route.ok(cap, R.Step.route(H.Route.reshape(cap, r, k, h, t, out))) == True{} : Bool}

def ok_reshape(cap, r, k, h, t, out, eh, et):
  +m = Mk(cap, r, k, h, t)
  %Equal.sym(T.Route, R.Step.route(R.Step.add(out, m)), R.Step.route(m), step_route(out, m)) : {R.Route.ok(cap, _) == True{} : Bool}
  PR.ok_remake(cap, T.Route.crew(r), T.Route.day(r), k, h, t, eh, et)

law crew_reshape:
  for +cap: Nat
  for +r: T.Route
  for +k: Bool
  for +h: ST()
  for +t: ST()
  for +out: ST()
  {T.Route.crew(R.Step.route(H.Route.reshape(cap, r, k, h, t, out))) == T.Route.crew(r) : T.Contractor}

def crew_reshape(cap, r, k, h, t, out):
  +m = Mk(cap, r, k, h, t)
  %Equal.sym(T.Route, R.Step.route(R.Step.add(out, m)), R.Step.route(m), step_route(out, m)) : {T.Route.crew(_) == T.Route.crew(r) : T.Contractor}
  PR.crew_remake(cap, T.Route.crew(r), T.Route.day(r), k, h, t)

law day_reshape:
  for +cap: Nat
  for +r: T.Route
  for +k: Bool
  for +h: ST()
  for +t: ST()
  for +out: ST()
  {T.Route.day(R.Step.route(H.Route.reshape(cap, r, k, h, t, out))) == T.Route.day(r) : Nat}

def day_reshape(cap, r, k, h, t, out):
  +m = Mk(cap, r, k, h, t)
  %Equal.sym(T.Route, R.Step.route(R.Step.add(out, m)), R.Step.route(m), step_route(out, m)) : {T.Route.day(_) == T.Route.day(r) : Nat}
  PR.day_remake(cap, T.Route.crew(r), T.Route.day(r), k, h, t)

law locked_reshape:
  for +cap: Nat
  for +r: T.Route
  for +k: Bool
  for +h: ST()
  for +t: ST()
  for +out: ST()
  for +eh: {R.Stops.all_locked(h) == True{} : Bool}
  for +et: {R.Stops.all_open(t) == True{} : Bool}
  {R.Stops.locked(T.Route.stops(R.Step.route(H.Route.reshape(cap, r, k, h, t, out)))) == h : ST()}

def locked_reshape(cap, r, k, h, t, out, eh, et):
  +m = Mk(cap, r, k, h, t)
  %Equal.sym(T.Route, R.Step.route(R.Step.add(out, m)), R.Step.route(m), step_route(out, m)) : {R.Stops.locked(T.Route.stops(_)) == h : ST()}
  PR.locked_remake(cap, T.Route.crew(r), T.Route.day(r), k, h, t, eh, et)

law jc_reshape:
  for +a: T.Appraisal
  for +cap: Nat
  for +r: T.Route
  for +k: Bool
  for +h: ST()
  for +t: ST()
  for +out: ST()
  {Nat.add(JC(a, T.Route.stops(R.Step.route(H.Route.reshape(cap, r, k, h, t, out)))), JC(a, R.Step.shed(H.Route.reshape(cap, r, k, h, t, out)))) == Nat.add(JC(a, out), Nat.add(JC(a, h), JC(a, t))) : Nat}

def jc_reshape(a, cap, r, k, h, t, out):
  +m = Mk(cap, r, k, h, t)
  +rs = H.Route.reshape(cap, r, k, h, t, out)
  +x = JC(a, T.Route.stops(R.Step.route(m)))
  +y = JC(a, R.Step.shed(m))
  %Equal.sym(T.Route, R.Step.route(R.Step.add(out, m)), R.Step.route(m), step_route(out, m)) : {Nat.add(JC(a, T.Route.stops(_)), JC(a, R.Step.shed(rs))) == Nat.add(JC(a, out), Nat.add(JC(a, h), JC(a, t))) : Nat}
  %Equal.sym(ST(), R.Step.shed(R.Step.add(out, m)), R.Stops.append(out, R.Step.shed(m)), step_shed(out, m)) : {Nat.add(x, JC(a, _)) == Nat.add(JC(a, out), Nat.add(JC(a, h), JC(a, t))) : Nat}
  Equal.trans(Nat, Nat.add(x, JC(a, R.Stops.append(out, R.Step.shed(m)))), Nat.add(x, Nat.add(JC(a, out), y)),
    Nat.add(JC(a, out), Nat.add(JC(a, h), JC(a, t))),
    L.add_r(x, JC(a, R.Stops.append(out, R.Step.shed(m))), Nat.add(JC(a, out), y), PR.jc_append(a, out, R.Step.shed(m))),
    Equal.trans(Nat, Nat.add(x, Nat.add(JC(a, out), y)), Nat.add(JC(a, out), Nat.add(x, y)),
      Nat.add(JC(a, out), Nat.add(JC(a, h), JC(a, t))),
      L.add_swap(x, JC(a, out), y),
      L.add_r(JC(a, out), Nat.add(x, y), Nat.add(JC(a, h), JC(a, t)),
        PR.jc_remake(a, cap, T.Route.crew(r), T.Route.day(r), k, h, t))))

law open_t:
  for +cap: Nat
  for +r: T.Route
  for +e: {R.Route.ok(cap, r) == True{} : Bool}
  {R.Stops.all_open(H.Route.t(r)) == True{} : Bool}

def open_t(cap, r, e):
  match r:
    case T.Route{c, d, s, k, a}:
      L.and_l(R.Stops.all_open(R.Stops.tail(s)), Bool.and(T.Audit.is_eq(a, R.Audit.of(c, d, s)), Nat.is_le(T.Audit.extra(a), cap)), e)

law bag_route:
  for +a: T.Appraisal
  for +r: T.Route
  {Nat.add(JC(a, H.Route.h(r)), JC(a, H.Route.t(r))) == JC(a, T.Route.stops(r)) : Nat}

def bag_route(a, r):
  PR.jc_head_tail(a, T.Route.stops(r))

law locked_h:
  for +r: T.Route
  {R.Stops.all_locked(H.Route.h(r)) == True{} : Bool}

def locked_h(r):
  PR.locked_head(T.Route.stops(r))

law locked_is_h:
  for +cap: Nat
  for +r: T.Route
  for +e: {R.Route.ok(cap, r) == True{} : Bool}
  {H.Route.h(r) == R.Stops.locked(T.Route.stops(r)) : ST()}

def locked_is_h(cap, r, e):
  Equal.sym(ST(), R.Stops.locked(T.Route.stops(r)), H.Route.h(r), PR.locked_is_head(T.Route.stops(r), open_t(cap, r, e)))

# Lifecycle steps on stops
# ------------------------

law started_locked:
  for +s: T.Stop
  for +e: {R.Stop.open(s) == True{} : Bool}
  {R.Stop.locked(H.Stop.start(s)) == True{} : Bool}

def started_locked(s, e):
  match s:
    case T.Stop{j, T.Open{}}:
      {==}
    case T.Stop{j, T.Underway{}}:
      {==}
    case T.Stop{j, T.Completed{}}:
      {==}
    case T.Stop{j, T.Failed{}}:
      L.never({False{} == True{} : Bool}, e)
    case T.Stop{j, T.Cancelled{}}:
      L.never({False{} == True{} : Bool}, e)

law start_all:
  for +xs: ST()
  for +e: {R.Stops.all_open(xs) == True{} : Bool}
  {R.Stops.all_locked(H.Stops.start(xs)) == True{} : Bool}

def start_all(xs, e):
  match xs:
    case Nil{}:
      {==}
    case +s <> r:
      L.and_i(R.Stop.locked(H.Stop.start(s)), R.Stops.all_locked(H.Stops.start(r)),
        started_locked(s, L.and_l(R.Stop.open(s), R.Stops.all_open(r), e)),
        start_all(r, L.and_r(R.Stop.open(s), R.Stops.all_open(r), e)))

law start_job:
  for +s: T.Stop
  {T.Stop.job(H.Stop.start(s)) == T.Stop.job(s) : T.Appraisal}

def start_job(s):
  match s:
    case T.Stop{j, t}:
      {==}

law start_jobs:
  for +xs: ST()
  {R.Stops.jobs(H.Stops.start(xs)) == R.Stops.jobs(xs) : List<&2, T.Appraisal>}

def start_jobs(xs):
  match xs:
    case Nil{}:
      {==}
    case +s <> r:
      %start_job(s) : {T.Stop.job(H.Stop.start(s)) <> R.Stops.jobs(H.Stops.start(r)) == _ <> R.Stops.jobs(r) : List<&2, T.Appraisal>}
      %start_jobs(r) : {T.Stop.job(H.Stop.start(s)) <> R.Stops.jobs(H.Stops.start(r)) == T.Stop.job(H.Stop.start(s)) <> _ : List<&2, T.Appraisal>}
      {==}

law finish_locked:
  for +c: Bool
  for +s: T.Stop
  for +e: {R.Stop.locked(s) == True{} : Bool}
  {R.Stop.locked(H.Stop.finish.if(c, s)) == True{} : Bool}

def finish_locked(c, s, e):
  match c:
    case True{}:
      {==}
    case False{}:
      e

law finish_all:
  for +xs: ST()
  for +i: Nat
  for +e: {R.Stops.all_locked(xs) == True{} : Bool}
  {R.Stops.all_locked(H.Stops.finish(xs, i)) == True{} : Bool}

def finish_all(xs, i, e):
  match xs:
    case Nil{}:
      {==}
    case +s <> r:
      +c = R.Test.run(R.IsUnderway{i}, s)
      L.and_i(R.Stop.locked(H.Stop.finish.if(c, s)), R.Stops.all_locked(H.Stops.finish(r, i)),
        finish_locked(c, s, L.and_l(R.Stop.locked(s), R.Stops.all_locked(r), e)),
        finish_all(r, i, L.and_r(R.Stop.locked(s), R.Stops.all_locked(r), e)))

law finish_job:
  for +c: Bool
  for +s: T.Stop
  {T.Stop.job(H.Stop.finish.if(c, s)) == T.Stop.job(s) : T.Appraisal}

def finish_job(c, s):
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

law finish_jobs:
  for +xs: ST()
  for +i: Nat
  {R.Stops.jobs(H.Stops.finish(xs, i)) == R.Stops.jobs(xs) : List<&2, T.Appraisal>}

def finish_jobs(xs, i):
  match xs:
    case Nil{}:
      {==}
    case +s <> r:
      +c = R.Test.run(R.IsUnderway{i}, s)
      %finish_job(c, s) : {T.Stop.job(H.Stop.finish.if(c, s)) <> R.Stops.jobs(H.Stops.finish(r, i)) == _ <> R.Stops.jobs(r) : List<&2, T.Appraisal>}
      %finish_jobs(r, i) : {T.Stop.job(H.Stop.finish.if(c, s)) <> R.Stops.jobs(H.Stops.finish(r, i)) == T.Stop.job(H.Stop.finish.if(c, s)) <> _ : List<&2, T.Appraisal>}
      {==}

law jc_of_jobs:
  for +a: T.Appraisal
  for -xs: ST()
  for -ys: ST()
  for e: {R.Stops.jobs(xs) == R.Stops.jobs(ys) : List<&2, T.Appraisal>}
  {JC(a, xs) == JC(a, ys) : Nat}

def jc_of_jobs(a, xs, ys, e):
  %e : {J.count(a, R.Stops.jobs(xs)) == J.count(a, _) : Nat}
  {==}

# Each edit keeps a valid route valid
# -----------------------------------

law ok_pull:
  for +c: Bool
  for +cap: Nat
  for +r: T.Route
  for +i: Nat
  for +e: {R.Route.ok(cap, r) == True{} : Bool}
  {R.Route.ok(cap, R.Step.route(H.Pull.if(c, cap, r, i))) == True{} : Bool}

def ok_pull(c, cap, r, i, e):
  match c:
    case True{}:
      ok_reshape(cap, r, T.Route.closed(r), H.Route.h(r), R.Stops.cut(H.Route.t(r), R.HasId{i}), R.Stops.keep(H.Route.t(r), R.HasId{i}),
        locked_h(r), PR.open_cut(H.Route.t(r), R.HasId{i}, open_t(cap, r, e)))
    case False{}:
      e

law ok_clear:
  for +c: Bool
  for +cap: Nat
  for +r: T.Route
  for +e: {R.Route.ok(cap, r) == True{} : Bool}
  {R.Route.ok(cap, R.Step.route(H.Clear.if(c, cap, r))) == True{} : Bool}

def ok_clear(c, cap, r, e):
  match c:
    case True{}:
      ok_reshape(cap, r, True{}, H.Route.h(r), Nil{}, H.Route.t(r), locked_h(r), {==})
    case False{}:
      e

law ok_reorder:
  for +c: Bool
  for +x: Bool
  for +cap: Nat
  for +r: T.Route
  for +n: ST()
  for +e: {R.Route.ok(cap, r) == True{} : Bool}
  for +g: {Bool.and(x, H.Stops.same_bag(n, H.Route.t(r))) == c : Bool}
  {R.Route.ok(cap, R.Step.route(H.Reorder.if(c, cap, r, n))) == True{} : Bool}

def ok_reorder(c, x, cap, r, n, e, g):
  match c:
    case True{}:
      +b = J.same(J.sort(R.Stops.jobs(n)), J.sort(R.Stops.jobs(H.Route.t(r))))
      ok_reshape(cap, r, T.Route.closed(r), H.Route.h(r), n, Nil{}, locked_h(r),
        L.and_l(R.Stops.all_open(n), b, L.and_r(x, H.Stops.same_bag(n, H.Route.t(r)), g)))
    case False{}:
      e

law ok_begin:
  for +c: Bool
  for +cap: Nat
  for +r: T.Route
  for +i: Nat
  for +e: {R.Route.ok(cap, r) == True{} : Bool}
  {R.Route.ok(cap, R.Step.route(H.Begin.if(c, cap, r, i))) == True{} : Bool}

def ok_begin(c, cap, r, i, e):
  match c:
    case True{}:
      +t = H.Route.t(r)
      +z = {R.HasId{i} : R.Test}
      ok_reshape(cap, r, T.Route.closed(r), R.Stops.append(H.Route.h(r), H.Stops.start(R.Stops.keep(t, z))), R.Stops.cut(t, z), Nil{},
        PR.locked_append(H.Route.h(r), H.Stops.start(R.Stops.keep(t, z)), locked_h(r), start_all(R.Stops.keep(t, z), PR.open_keep(t, z, open_t(cap, r, e)))),
        PR.open_cut(t, z, open_t(cap, r, e)))
    case False{}:
      e

law ok_finish:
  for +c: Bool
  for +cap: Nat
  for +r: T.Route
  for +i: Nat
  for +e: {R.Route.ok(cap, r) == True{} : Bool}
  {R.Route.ok(cap, R.Step.route(H.Finish.if(c, cap, r, i))) == True{} : Bool}

def ok_finish(c, cap, r, i, e):
  match c:
    case True{}:
      ok_reshape(cap, r, T.Route.closed(r), H.Stops.finish(H.Route.h(r), i), H.Route.t(r), Nil{},
        finish_all(H.Route.h(r), i, locked_h(r)), open_t(cap, r, e))
    case False{}:
      e

law ok_abandon:
  for +c: Bool
  for +cap: Nat
  for +r: T.Route
  for +i: Nat
  for +e: {R.Route.ok(cap, r) == True{} : Bool}
  {R.Route.ok(cap, R.Step.route(H.Abandon.if(c, cap, r, i))) == True{} : Bool}

def ok_abandon(c, cap, r, i, e):
  match c:
    case True{}:
      +h = H.Route.h(r)
      +z = {R.IsUnderway{i} : R.Test}
      ok_reshape(cap, r, T.Route.closed(r), R.Stops.cut(h, z), H.Route.t(r), R.Stops.keep(h, z),
        PR.locked_cut(h, z, locked_h(r)), open_t(cap, r, e))
    case False{}:
      e

law ok_apply:
  for +cap: Nat
  for +e: H.Edit
  for +r: T.Route
  for +er: {R.Route.ok(cap, r) == True{} : Bool}
  {R.Route.ok(cap, R.Step.route(H.Route.apply(cap, e, r))) == True{} : Bool}

def ok_apply(cap, e, r, er):
  match e:
    case H.Pull{i}:
      ok_pull(R.Stops.any(H.Route.t(r), R.HasId{i}), cap, r, i, er)
    case H.Clear{c, d}:
      ok_clear(H.Route.at(r, c, d), cap, r, er)
    case H.Reorder{c, d, n}:
      ok_reorder(Bool.and(H.Route.at(r, c, d), H.Stops.same_bag(n, H.Route.t(r))), H.Route.at(r, c, d), cap, r, n, er, {==})
    case H.Begin{i}:
      ok_begin(R.Stops.any(H.Route.t(r), R.HasId{i}), cap, r, i, er)
    case H.Finish{i}:
      ok_finish(R.Stops.any(H.Route.h(r), R.IsUnderway{i}), cap, r, i, er)
    case H.Abandon{i}:
      ok_abandon(R.Stops.any(H.Route.h(r), R.IsUnderway{i}), cap, r, i, er)

# Each edit loses nothing
# -----------------------

def Bag(+a: T.Appraisal, +s: R.Step) -> Nat:
  Nat.add(JC(a, T.Route.stops(R.Step.route(s))), JC(a, R.Step.shed(s)))

law bag_same:
  for +a: T.Appraisal
  for +r: T.Route
  {Bag(a, R.Step{r, Nil{}}) == JC(a, T.Route.stops(r)) : Nat}

def bag_same(a, r):
  L.add_zero(JC(a, T.Route.stops(r)))

law jc_pull:
  for +a: T.Appraisal
  for +c: Bool
  for +cap: Nat
  for +r: T.Route
  for +i: Nat
  {Bag(a, H.Pull.if(c, cap, r, i)) == JC(a, T.Route.stops(r)) : Nat}

def jc_pull(a, c, cap, r, i):
  match c:
    case True{}:
      +h = H.Route.h(r)
      +t = H.Route.t(r)
      +z = {R.HasId{i} : R.Test}
      +kp = R.Stops.keep(t, z)
      +ct = R.Stops.cut(t, z)
      Equal.trans(Nat, Bag(a, H.Route.reshape(cap, r, T.Route.closed(r), h, ct, kp)), Nat.add(JC(a, kp), Nat.add(JC(a, h), JC(a, ct))),
        JC(a, T.Route.stops(r)),
        jc_reshape(a, cap, r, T.Route.closed(r), h, ct, kp),
        Equal.trans(Nat, Nat.add(JC(a, kp), Nat.add(JC(a, h), JC(a, ct))), Nat.add(JC(a, h), Nat.add(JC(a, kp), JC(a, ct))),
          JC(a, T.Route.stops(r)),
          L.add_swap(JC(a, kp), JC(a, h), JC(a, ct)),
          Equal.trans(Nat, Nat.add(JC(a, h), Nat.add(JC(a, kp), JC(a, ct))), Nat.add(JC(a, h), JC(a, t)), JC(a, T.Route.stops(r)),
            L.add_r(JC(a, h), Nat.add(JC(a, kp), JC(a, ct)), JC(a, t), PR.jc_split(a, t, z)),
            bag_route(a, r))))
    case False{}:
      bag_same(a, r)

law jc_clear:
  for +a: T.Appraisal
  for +c: Bool
  for +cap: Nat
  for +r: T.Route
  {Bag(a, H.Clear.if(c, cap, r)) == JC(a, T.Route.stops(r)) : Nat}

def jc_clear(a, c, cap, r):
  match c:
    case True{}:
      +h = H.Route.h(r)
      +t = H.Route.t(r)
      Equal.trans(Nat, Bag(a, H.Route.reshape(cap, r, True{}, h, Nil{}, t)), Nat.add(JC(a, t), Nat.add(JC(a, h), 0n)),
        JC(a, T.Route.stops(r)),
        jc_reshape(a, cap, r, True{}, h, Nil{}, t),
        Equal.trans(Nat, Nat.add(JC(a, t), Nat.add(JC(a, h), 0n)), Nat.add(JC(a, t), JC(a, h)), JC(a, T.Route.stops(r)),
          L.add_r(JC(a, t), Nat.add(JC(a, h), 0n), JC(a, h), L.add_zero(JC(a, h))),
          Equal.trans(Nat, Nat.add(JC(a, t), JC(a, h)), Nat.add(JC(a, h), JC(a, t)), JC(a, T.Route.stops(r)),
            L.add_comm(JC(a, t), JC(a, h)), bag_route(a, r))))
    case False{}:
      bag_same(a, r)

# A same_bag guard means the same counts.
law jc_same_bag:
  for +a: T.Appraisal
  for +n: ST()
  for +t: ST()
  for +e: {H.Stops.same_bag(n, t) == True{} : Bool}
  {JC(a, n) == JC(a, t) : Nat}

def jc_same_bag(a, n, t, e):
  +jn = R.Stops.jobs(n)
  +jt = R.Stops.jobs(t)
  Equal.trans(Nat, J.count(a, jn), J.count(a, J.sort(jt)), J.count(a, jt),
    PJ.count_of_same(a, jn, J.sort(jt), L.and_r(R.Stops.all_open(n), J.same(J.sort(jn), J.sort(jt)), e)),
    PJ.count_sort(a, jt))

law jc_reorder:
  for +a: T.Appraisal
  for +c: Bool
  for +x: Bool
  for +cap: Nat
  for +r: T.Route
  for +n: ST()
  for +g: {Bool.and(x, H.Stops.same_bag(n, H.Route.t(r))) == c : Bool}
  {Bag(a, H.Reorder.if(c, cap, r, n)) == JC(a, T.Route.stops(r)) : Nat}

def jc_reorder(a, c, x, cap, r, n, g):
  match c:
    case True{}:
      +h = H.Route.h(r)
      +t = H.Route.t(r)
      Equal.trans(Nat, Bag(a, H.Route.reshape(cap, r, T.Route.closed(r), h, n, Nil{})), Nat.add(JC(a, h), JC(a, n)),
        JC(a, T.Route.stops(r)),
        jc_reshape(a, cap, r, T.Route.closed(r), h, n, Nil{}),
        Equal.trans(Nat, Nat.add(JC(a, h), JC(a, n)), Nat.add(JC(a, h), JC(a, t)), JC(a, T.Route.stops(r)),
          L.add_r(JC(a, h), JC(a, n), JC(a, t), jc_same_bag(a, n, t, L.and_r(x, H.Stops.same_bag(n, t), g))),
          bag_route(a, r)))
    case False{}:
      bag_same(a, r)

law jc_begin:
  for +a: T.Appraisal
  for +c: Bool
  for +cap: Nat
  for +r: T.Route
  for +i: Nat
  {Bag(a, H.Begin.if(c, cap, r, i)) == JC(a, T.Route.stops(r)) : Nat}

def jc_begin(a, c, cap, r, i):
  match c:
    case True{}:
      +h = H.Route.h(r)
      +t = H.Route.t(r)
      +z = {R.HasId{i} : R.Test}
      +kp = R.Stops.keep(t, z)
      +ct = R.Stops.cut(t, z)
      +st = H.Stops.start(kp)
      Equal.trans(Nat, Bag(a, H.Route.reshape(cap, r, T.Route.closed(r), R.Stops.append(h, st), ct, Nil{})),
        Nat.add(JC(a, R.Stops.append(h, st)), JC(a, ct)), JC(a, T.Route.stops(r)),
        jc_reshape(a, cap, r, T.Route.closed(r), R.Stops.append(h, st), ct, Nil{}),
        Equal.trans(Nat, Nat.add(JC(a, R.Stops.append(h, st)), JC(a, ct)), Nat.add(Nat.add(JC(a, h), JC(a, st)), JC(a, ct)),
          JC(a, T.Route.stops(r)),
          L.add_l(JC(a, R.Stops.append(h, st)), Nat.add(JC(a, h), JC(a, st)), JC(a, ct), PR.jc_append(a, h, st)),
          Equal.trans(Nat, Nat.add(Nat.add(JC(a, h), JC(a, st)), JC(a, ct)), Nat.add(JC(a, h), Nat.add(JC(a, st), JC(a, ct))),
            JC(a, T.Route.stops(r)),
            L.add_assoc(JC(a, h), JC(a, st), JC(a, ct)),
            Equal.trans(Nat, Nat.add(JC(a, h), Nat.add(JC(a, st), JC(a, ct))), Nat.add(JC(a, h), Nat.add(JC(a, kp), JC(a, ct))),
              JC(a, T.Route.stops(r)),
              L.add_r(JC(a, h), Nat.add(JC(a, st), JC(a, ct)), Nat.add(JC(a, kp), JC(a, ct)),
                L.add_l(JC(a, st), JC(a, kp), JC(a, ct), jc_of_jobs(a, st, kp, start_jobs(kp)))),
              Equal.trans(Nat, Nat.add(JC(a, h), Nat.add(JC(a, kp), JC(a, ct))), Nat.add(JC(a, h), JC(a, t)), JC(a, T.Route.stops(r)),
                L.add_r(JC(a, h), Nat.add(JC(a, kp), JC(a, ct)), JC(a, t), PR.jc_split(a, t, z)),
                bag_route(a, r))))))
    case False{}:
      bag_same(a, r)

law jc_finish:
  for +a: T.Appraisal
  for +c: Bool
  for +cap: Nat
  for +r: T.Route
  for +i: Nat
  {Bag(a, H.Finish.if(c, cap, r, i)) == JC(a, T.Route.stops(r)) : Nat}

def jc_finish(a, c, cap, r, i):
  match c:
    case True{}:
      +h = H.Route.h(r)
      +t = H.Route.t(r)
      +f = H.Stops.finish(h, i)
      Equal.trans(Nat, Bag(a, H.Route.reshape(cap, r, T.Route.closed(r), f, t, Nil{})), Nat.add(JC(a, f), JC(a, t)),
        JC(a, T.Route.stops(r)),
        jc_reshape(a, cap, r, T.Route.closed(r), f, t, Nil{}),
        Equal.trans(Nat, Nat.add(JC(a, f), JC(a, t)), Nat.add(JC(a, h), JC(a, t)), JC(a, T.Route.stops(r)),
          L.add_l(JC(a, f), JC(a, h), JC(a, t), jc_of_jobs(a, f, h, finish_jobs(h, i))),
          bag_route(a, r)))
    case False{}:
      bag_same(a, r)

law jc_abandon:
  for +a: T.Appraisal
  for +c: Bool
  for +cap: Nat
  for +r: T.Route
  for +i: Nat
  {Bag(a, H.Abandon.if(c, cap, r, i)) == JC(a, T.Route.stops(r)) : Nat}

def jc_abandon(a, c, cap, r, i):
  match c:
    case True{}:
      +h = H.Route.h(r)
      +t = H.Route.t(r)
      +z = {R.IsUnderway{i} : R.Test}
      +kp = R.Stops.keep(h, z)
      +ct = R.Stops.cut(h, z)
      Equal.trans(Nat, Bag(a, H.Route.reshape(cap, r, T.Route.closed(r), ct, t, kp)), Nat.add(JC(a, kp), Nat.add(JC(a, ct), JC(a, t))),
        JC(a, T.Route.stops(r)),
        jc_reshape(a, cap, r, T.Route.closed(r), ct, t, kp),
        Equal.trans(Nat, Nat.add(JC(a, kp), Nat.add(JC(a, ct), JC(a, t))), Nat.add(Nat.add(JC(a, kp), JC(a, ct)), JC(a, t)),
          JC(a, T.Route.stops(r)),
          Equal.sym(Nat, Nat.add(Nat.add(JC(a, kp), JC(a, ct)), JC(a, t)), Nat.add(JC(a, kp), Nat.add(JC(a, ct), JC(a, t))),
            L.add_assoc(JC(a, kp), JC(a, ct), JC(a, t))),
          Equal.trans(Nat, Nat.add(Nat.add(JC(a, kp), JC(a, ct)), JC(a, t)), Nat.add(JC(a, h), JC(a, t)), JC(a, T.Route.stops(r)),
            L.add_l(Nat.add(JC(a, kp), JC(a, ct)), JC(a, h), JC(a, t), PR.jc_split(a, h, z)),
            bag_route(a, r))))
    case False{}:
      bag_same(a, r)

law jc_apply:
  for +a: T.Appraisal
  for +cap: Nat
  for +e: H.Edit
  for +r: T.Route
  {Bag(a, H.Route.apply(cap, e, r)) == JC(a, T.Route.stops(r)) : Nat}

def jc_apply(a, cap, e, r):
  match e:
    case H.Pull{i}:
      jc_pull(a, R.Stops.any(H.Route.t(r), R.HasId{i}), cap, r, i)
    case H.Clear{c, d}:
      jc_clear(a, H.Route.at(r, c, d), cap, r)
    case H.Reorder{c, d, n}:
      jc_reorder(a, Bool.and(H.Route.at(r, c, d), H.Stops.same_bag(n, H.Route.t(r))), H.Route.at(r, c, d), cap, r, n, {==})
    case H.Begin{i}:
      jc_begin(a, R.Stops.any(H.Route.t(r), R.HasId{i}), cap, r, i)
    case H.Finish{i}:
      jc_finish(a, R.Stops.any(H.Route.h(r), R.IsUnderway{i}), cap, r, i)
    case H.Abandon{i}:
      jc_abandon(a, R.Stops.any(H.Route.h(r), R.IsUnderway{i}), cap, r, i)

# Each edit keeps the crew and the day
# ------------------------------------

def Keeps(+s: R.Step, +r: T.Route) -> Type:
  {T.Route.crew(R.Step.route(s)) == T.Route.crew(r) : T.Contractor} & {T.Route.day(R.Step.route(s)) == T.Route.day(r) : Nat}

law keeps_reshape:
  for +cap: Nat
  for +r: T.Route
  for +k: Bool
  for +h: ST()
  for +t: ST()
  for +out: ST()
  Keeps(H.Route.reshape(cap, r, k, h, t, out), r)

def keeps_reshape(cap, r, k, h, t, out):
  (crew_reshape(cap, r, k, h, t, out), day_reshape(cap, r, k, h, t, out))

law keeps_pull:
  for +c: Bool
  for +cap: Nat
  for +r: T.Route
  for +i: Nat
  Keeps(H.Pull.if(c, cap, r, i), r)

def keeps_pull(c, cap, r, i):
  match c:
    case True{}:
      keeps_reshape(cap, r, T.Route.closed(r), H.Route.h(r), R.Stops.cut(H.Route.t(r), R.HasId{i}), R.Stops.keep(H.Route.t(r), R.HasId{i}))
    case False{}:
      ({==}, {==})

law keeps_clear:
  for +c: Bool
  for +cap: Nat
  for +r: T.Route
  Keeps(H.Clear.if(c, cap, r), r)

def keeps_clear(c, cap, r):
  match c:
    case True{}:
      keeps_reshape(cap, r, True{}, H.Route.h(r), Nil{}, H.Route.t(r))
    case False{}:
      ({==}, {==})

law keeps_reorder:
  for +c: Bool
  for +cap: Nat
  for +r: T.Route
  for +n: ST()
  Keeps(H.Reorder.if(c, cap, r, n), r)

def keeps_reorder(c, cap, r, n):
  match c:
    case True{}:
      keeps_reshape(cap, r, T.Route.closed(r), H.Route.h(r), n, Nil{})
    case False{}:
      ({==}, {==})

law keeps_begin:
  for +c: Bool
  for +cap: Nat
  for +r: T.Route
  for +i: Nat
  Keeps(H.Begin.if(c, cap, r, i), r)

def keeps_begin(c, cap, r, i):
  match c:
    case True{}:
      keeps_reshape(cap, r, T.Route.closed(r), R.Stops.append(H.Route.h(r), H.Stops.start(R.Stops.keep(H.Route.t(r), R.HasId{i}))), R.Stops.cut(H.Route.t(r), R.HasId{i}), Nil{})
    case False{}:
      ({==}, {==})

law keeps_finish:
  for +c: Bool
  for +cap: Nat
  for +r: T.Route
  for +i: Nat
  Keeps(H.Finish.if(c, cap, r, i), r)

def keeps_finish(c, cap, r, i):
  match c:
    case True{}:
      keeps_reshape(cap, r, T.Route.closed(r), H.Stops.finish(H.Route.h(r), i), H.Route.t(r), Nil{})
    case False{}:
      ({==}, {==})

law keeps_abandon:
  for +c: Bool
  for +cap: Nat
  for +r: T.Route
  for +i: Nat
  Keeps(H.Abandon.if(c, cap, r, i), r)

def keeps_abandon(c, cap, r, i):
  match c:
    case True{}:
      keeps_reshape(cap, r, T.Route.closed(r), R.Stops.cut(H.Route.h(r), R.IsUnderway{i}), H.Route.t(r), R.Stops.keep(H.Route.h(r), R.IsUnderway{i}))
    case False{}:
      ({==}, {==})

law keeps_apply:
  for +cap: Nat
  for +e: H.Edit
  for +r: T.Route
  Keeps(H.Route.apply(cap, e, r), r)

def keeps_apply(cap, e, r):
  match e:
    case H.Pull{i}:
      keeps_pull(R.Stops.any(H.Route.t(r), R.HasId{i}), cap, r, i)
    case H.Clear{c, d}:
      keeps_clear(H.Route.at(r, c, d), cap, r)
    case H.Reorder{c, d, n}:
      keeps_reorder(Bool.and(H.Route.at(r, c, d), H.Stops.same_bag(n, H.Route.t(r))), cap, r, n)
    case H.Begin{i}:
      keeps_begin(R.Stops.any(H.Route.t(r), R.HasId{i}), cap, r, i)
    case H.Finish{i}:
      keeps_finish(R.Stops.any(H.Route.h(r), R.IsUnderway{i}), cap, r, i)
    case H.Abandon{i}:
      keeps_abandon(R.Stops.any(H.Route.h(r), R.IsUnderway{i}), cap, r, i)

# The healing edits leave locked stops alone
# ------------------------------------------

def Heals(e: H.Edit) -> Bool:
  match e:
    case H.Pull{i}:
      True{}
    case H.Clear{c, d}:
      True{}
    case H.Reorder{c, d, n}:
      True{}
    case _:
      False{}

def Lk(s: R.Step) -> ST():
  R.Stops.locked(T.Route.stops(R.Step.route(s)))

law locked_pull:
  for +c: Bool
  for +cap: Nat
  for +r: T.Route
  for +i: Nat
  for +e: {R.Route.ok(cap, r) == True{} : Bool}
  {Lk(H.Pull.if(c, cap, r, i)) == R.Stops.locked(T.Route.stops(r)) : ST()}

def locked_pull(c, cap, r, i, e):
  match c:
    case True{}:
      Equal.trans(ST(), Lk(H.Route.reshape(cap, r, T.Route.closed(r), H.Route.h(r), R.Stops.cut(H.Route.t(r), R.HasId{i}), R.Stops.keep(H.Route.t(r), R.HasId{i}))),
        H.Route.h(r), R.Stops.locked(T.Route.stops(r)),
        locked_reshape(cap, r, T.Route.closed(r), H.Route.h(r), R.Stops.cut(H.Route.t(r), R.HasId{i}), R.Stops.keep(H.Route.t(r), R.HasId{i}),
          locked_h(r), PR.open_cut(H.Route.t(r), R.HasId{i}, open_t(cap, r, e))),
        locked_is_h(cap, r, e))
    case False{}:
      {==}

law locked_clear:
  for +c: Bool
  for +cap: Nat
  for +r: T.Route
  for +e: {R.Route.ok(cap, r) == True{} : Bool}
  {Lk(H.Clear.if(c, cap, r)) == R.Stops.locked(T.Route.stops(r)) : ST()}

def locked_clear(c, cap, r, e):
  match c:
    case True{}:
      Equal.trans(ST(), Lk(H.Route.reshape(cap, r, True{}, H.Route.h(r), Nil{}, H.Route.t(r))),
        H.Route.h(r), R.Stops.locked(T.Route.stops(r)),
        locked_reshape(cap, r, True{}, H.Route.h(r), Nil{}, H.Route.t(r), locked_h(r), {==}),
        locked_is_h(cap, r, e))
    case False{}:
      {==}

law locked_reorder:
  for +c: Bool
  for +x: Bool
  for +cap: Nat
  for +r: T.Route
  for +n: ST()
  for +e: {R.Route.ok(cap, r) == True{} : Bool}
  for +g: {Bool.and(x, H.Stops.same_bag(n, H.Route.t(r))) == c : Bool}
  {Lk(H.Reorder.if(c, cap, r, n)) == R.Stops.locked(T.Route.stops(r)) : ST()}

def locked_reorder(c, x, cap, r, n, e, g):
  match c:
    case True{}:
      +b = J.same(J.sort(R.Stops.jobs(n)), J.sort(R.Stops.jobs(H.Route.t(r))))
      Equal.trans(ST(), Lk(H.Route.reshape(cap, r, T.Route.closed(r), H.Route.h(r), n, Nil{})),
        H.Route.h(r), R.Stops.locked(T.Route.stops(r)),
        locked_reshape(cap, r, T.Route.closed(r), H.Route.h(r), n, Nil{}, locked_h(r),
          L.and_l(R.Stops.all_open(n), b, L.and_r(x, H.Stops.same_bag(n, H.Route.t(r)), g))),
        locked_is_h(cap, r, e))
    case False{}:
      {==}

law locked_apply:
  for +cap: Nat
  for +e: H.Edit
  for +r: T.Route
  for +er: {R.Route.ok(cap, r) == True{} : Bool}
  for +eh: {Heals(e) == True{} : Bool}
  {Lk(H.Route.apply(cap, e, r)) == R.Stops.locked(T.Route.stops(r)) : ST()}

def locked_apply(cap, e, r, er, eh):
  match e:
    case H.Pull{i}:
      locked_pull(R.Stops.any(H.Route.t(r), R.HasId{i}), cap, r, i, er)
    case H.Clear{c, d}:
      locked_clear(H.Route.at(r, c, d), cap, r, er)
    case H.Reorder{c, d, n}:
      locked_reorder(Bool.and(H.Route.at(r, c, d), H.Stops.same_bag(n, H.Route.t(r))), H.Route.at(r, c, d), cap, r, n, er, {==})
    case H.Begin{i}:
      L.never({Lk(H.Route.apply(cap, H.Begin{i}, r)) == R.Stops.locked(T.Route.stops(r)) : ST()}, eh)
    case H.Finish{i}:
      L.never({Lk(H.Route.apply(cap, H.Finish{i}, r)) == R.Stops.locked(T.Route.stops(r)) : ST()}, eh)
    case H.Abandon{i}:
      L.never({Lk(H.Route.apply(cap, H.Abandon{i}, r)) == R.Stops.locked(T.Route.stops(r)) : ST()}, eh)
