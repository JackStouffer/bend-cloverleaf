import Base
import ../core/types.bend as T
import ../core/jobs.bend as J
import ../core/route.bend as R
import ../core/plan.bend as P
import ../core/heal.bend as H
import ../core/solve.bend as S
import ./logic.bend as L
import ./jobs.bend as PJ
import ./plan.bend as PP

# The planner's guarantees: forking the search changes nothing, the parallel
# checker agrees with the sequential one, and what leaves the planner is valid.

def RL() -> Data:
  List<&2, T.Route>

def AL() -> Data:
  List<&2, T.Appraisal>

def MC() -> Data:
  Maybe<&2, S.Cand>

def Crews() -> Data:
  List<&2, T.Contractor>

# Picking the better candidate
# ----------------------------

def M(+x: S.Cand, +y: S.Cand) -> S.Cand:
  S.Cand.pick(Nat.is_lt(S.Cand.cost(y), S.Cand.cost(x)), x, y)

law m_t:
  for +x: S.Cand
  for +y: S.Cand
  for +e: {Nat.is_lt(S.Cand.cost(y), S.Cand.cost(x)) == True{} : Bool}
  {M(x, y) == y : S.Cand}

def m_t(x, y, e):
  %Equal.sym(Bool, Nat.is_lt(S.Cand.cost(y), S.Cand.cost(x)), True{}, e) : {S.Cand.pick(_, x, y) == y : S.Cand}
  {==}

law m_f:
  for +x: S.Cand
  for +y: S.Cand
  for +e: {Nat.is_lt(S.Cand.cost(y), S.Cand.cost(x)) == False{} : Bool}
  {M(x, y) == x : S.Cand}

def m_f(x, y, e):
  %Equal.sym(Bool, Nat.is_lt(S.Cand.cost(y), S.Cand.cost(x)), False{}, e) : {S.Cand.pick(_, x, y) == x : S.Cand}
  {==}

# Each case rewrites both sides down to the winning candidate.
law m_chain:
  for +l: S.Cand
  for +r: S.Cand
  for +w: S.Cand
  for +el: {l == w : S.Cand}
  for +er: {r == w : S.Cand}
  {l == r : S.Cand}

def m_chain(l, r, w, el, er):
  Equal.trans(S.Cand, l, w, r, el, Equal.sym(S.Cand, r, w, er))

law m_left:
  for +a: S.Cand
  for +b: S.Cand
  for +c: S.Cand
  for +e: {a == b : S.Cand}
  {M(a, c) == M(b, c) : S.Cand}

def m_left(a, b, c, e):
  Equal.cong(S.Cand, S.Cand, q => M(q, c), a, b, e)

law m_right:
  for +c: S.Cand
  for +a: S.Cand
  for +b: S.Cand
  for +e: {a == b : S.Cand}
  {M(c, a) == M(c, b) : S.Cand}

def m_right(c, a, b, e):
  Equal.cong(S.Cand, S.Cand, q => M(c, q), a, b, e)

def MA(+x: S.Cand, +y: S.Cand, +z: S.Cand) -> Type:
  {M(M(x, y), z) == M(x, M(y, z)) : S.Cand}

law m_assoc:
  for +x: S.Cand
  for +y: S.Cand
  for +z: S.Cand
  {M(M(x, y), z) == M(x, M(y, z)) : S.Cand}

def m_assoc(x, y, z):
  +cx = S.Cand.cost(x)
  +cy = S.Cand.cost(y)
  +cz = S.Cand.cost(z)
  L.cases(Nat.is_lt(cy, cx), MA(x, y, z),
    +a => L.cases(Nat.is_lt(cz, cy), MA(x, y, z),
      +b =>
        Equal.trans(S.Cand, M(M(x, y), z), M(y, z), M(x, M(y, z)), m_left(M(x, y), y, z, m_t(x, y, a)),
          Equal.trans(S.Cand, M(y, z), z, M(x, M(y, z)), m_t(y, z, b),
            Equal.sym(S.Cand, M(x, M(y, z)), z,
              Equal.trans(S.Cand, M(x, M(y, z)), M(x, z), z, m_right(x, M(y, z), z, m_t(y, z, b)),
                m_t(x, z, L.lt_trans(cz, cy, cx, b, a)))))),
      +b =>
        Equal.trans(S.Cand, M(M(x, y), z), M(y, z), M(x, M(y, z)), m_left(M(x, y), y, z, m_t(x, y, a)),
          Equal.trans(S.Cand, M(y, z), y, M(x, M(y, z)), m_f(y, z, b),
            Equal.sym(S.Cand, M(x, M(y, z)), y,
              Equal.trans(S.Cand, M(x, M(y, z)), M(x, y), y, m_right(x, M(y, z), y, m_f(y, z, b)), m_t(x, y, a)))))),
    +a => L.cases(Nat.is_lt(cz, cy), MA(x, y, z),
      +b =>
        Equal.trans(S.Cand, M(M(x, y), z), M(x, z), M(x, M(y, z)), m_left(M(x, y), x, z, m_f(x, y, a)),
          Equal.sym(S.Cand, M(x, M(y, z)), M(x, z), m_right(x, M(y, z), z, m_t(y, z, b)))),
      +b =>
        Equal.trans(S.Cand, M(M(x, y), z), M(x, z), M(x, M(y, z)), m_left(M(x, y), x, z, m_f(x, y, a)),
          Equal.trans(S.Cand, M(x, z), x, M(x, M(y, z)),
            L.cases(Nat.is_lt(cz, cx), {M(x, z) == x : S.Cand},
              +c => L.clash(Nat.is_lt(cz, cy), {M(x, z) == x : S.Cand}, L.lt_not_lt(cz, cx, cy, c, a), b),
              +c => m_f(x, z, c)),
            Equal.sym(S.Cand, M(x, M(y, z)), x,
              Equal.trans(S.Cand, M(x, M(y, z)), M(x, y), x, m_right(x, M(y, z), y, m_f(y, z, b)), m_f(x, y, a)))))))

law better_assoc:
  for +a: MC()
  for +b: MC()
  for +c: MC()
  {S.better(S.better(a, b), c) == S.better(a, S.better(b, c)) : MC()}

def better_assoc(a, b, c):
  match a b c:
    case None{} _ _:
      {==}
    case Some{x} None{} _:
      {==}
    case Some{x} Some{y} None{}:
      {==}
    case Some{x} Some{y} Some{z}:
      %m_assoc(x, y, z) : {Some{M(M(x, y), z)} == Some{_} : MC()}
      {==}

law seq_append:
  for +xs: RL()
  for +ys: RL()
  for +cap: Nat
  for +job: T.Appraisal
  for +outside: Bool
  {S.Select.seq(List.append(&2, T.Route, xs, ys), cap, job, outside) == S.better(S.Select.seq(xs, cap, job, outside), S.Select.seq(ys, cap, job, outside)) : MC()}

def seq_append(xs, ys, cap, job, outside):
  match xs:
    case Nil{}:
      {==}
    case +r <> t:
      +o = S.Select.one(cap, job, outside, r)
      +st = S.Select.seq(t, cap, job, outside)
      +sy = S.Select.seq(ys, cap, job, outside)
      Equal.trans(MC(), S.better(o, S.Select.seq(List.append(&2, T.Route, t, ys), cap, job, outside)), S.better(o, S.better(st, sy)), S.better(S.better(o, st), sy),
        Equal.cong(MC(), MC(), m => S.better(o, m), S.Select.seq(List.append(&2, T.Route, t, ys), cap, job, outside), S.better(st, sy), seq_append(t, ys, cap, job, outside)),
        Equal.sym(MC(), S.better(S.better(o, st), sy), S.better(o, S.better(st, sy)), better_assoc(o, st, sy)))

law tree_seq:
  for +t: S.Forest
  for +d: Nat
  for +cap: Nat
  for +job: T.Appraisal
  for +outside: Bool
  {S.Select.tree(t, d, cap, job, outside) == S.Select.seq(S.Forest.routes(t), cap, job, outside) : MC()}

law tree_fork:
  for +a: MC()
  for +b: MC()
  for +c: MC()
  for +d: MC()
  for +ea: {a == c : MC()}
  for +eb: {b == d : MC()}
  {S.better(a, b) == S.better(c, d) : MC()}

def tree_fork(a, b, c, d, ea, eb):
  %ea : {S.better(a, b) == S.better(_, d) : MC()}
  %eb : {S.better(a, b) == S.better(a, _) : MC()}
  {==}

def tree_seq(t, d, cap, job, outside):
  match t:
    case S.Bare{}:
      {==}
    case S.Leaf{r}:
      {==}
    case S.Fork{k, l, r}:
      match d:
        case 0n:
          +sl = S.Select.seq(S.Forest.routes(l), cap, job, outside)
          +sr = S.Select.seq(S.Forest.routes(r), cap, job, outside)
          +all = S.Select.seq(List.append(&2, T.Route, S.Forest.routes(l), S.Forest.routes(r)), cap, job, outside)
          Equal.trans(MC(), S.better(S.Select.tree(l, 0n, cap, job, outside), S.Select.tree(r, 0n, cap, job, outside)), S.better(sl, sr), all,
            tree_fork(S.Select.tree(l, 0n, cap, job, outside), S.Select.tree(r, 0n, cap, job, outside), sl, sr, tree_seq(l, 0n, cap, job, outside), tree_seq(r, 0n, cap, job, outside)),
            Equal.sym(MC(), all, S.better(sl, sr), seq_append(S.Forest.routes(l), S.Forest.routes(r), cap, job, outside)))
        case 1n+e:
          +sl = S.Select.seq(S.Forest.routes(l), cap, job, outside)
          +sr = S.Select.seq(S.Forest.routes(r), cap, job, outside)
          +all = S.Select.seq(List.append(&2, T.Route, S.Forest.routes(l), S.Forest.routes(r)), cap, job, outside)
          Equal.trans(MC(), S.better(S.Select.tree(l, e, cap, job, outside), S.Select.tree(r, e, cap, job, outside)), S.better(sl, sr), all,
            tree_fork(S.Select.tree(l, e, cap, job, outside), S.Select.tree(r, e, cap, job, outside), sl, sr, tree_seq(l, e, cap, job, outside), tree_seq(r, e, cap, job, outside)),
            Equal.sym(MC(), all, S.better(sl, sr), seq_append(S.Forest.routes(l), S.Forest.routes(r), cap, job, outside)))

# The parallel checker
# --------------------

law take_drop:
  for -A: Data
  for +xs: List<&2, A>
  for +n: Nat
  {List.append(&2, A, List.take(&2, A, xs, n), List.drop(&2, A, xs, n)) == xs : List<&2, A>}

def take_drop(A, xs, n):
  match xs n:
    case Nil{} _:
      {==}
    case h <> t 0n:
      {==}
    case +h <> t 1n+p:
      %take_drop(A, t, p) : {h <> List.append(&2, A, List.take(&2, A, t, p), List.drop(&2, A, t, p)) == h <> _ : List<&2, A>}
      {==}

law ok_append:
  for +xs: RL()
  for +ys: RL()
  for +crews: Crews()
  for +cap: Nat
  {P.Routes.ok(List.append(&2, T.Route, xs, ys), crews, cap) == Bool.and(P.Routes.ok(xs, crews, cap), P.Routes.ok(ys, crews, cap)) : Bool}

def ok_append(xs, ys, crews, cap):
  match xs:
    case Nil{}:
      {==}
    case +r <> t:
      +f = P.Route.fine(crews, cap, r)
      +o = P.Routes.ok(t, crews, cap)
      +y = P.Routes.ok(ys, crews, cap)
      Equal.trans(Bool, Bool.and(f, P.Routes.ok(List.append(&2, T.Route, t, ys), crews, cap)), Bool.and(f, Bool.and(o, y)), Bool.and(Bool.and(f, o), y),
        Equal.cong(Bool, Bool, b => Bool.and(f, b), P.Routes.ok(List.append(&2, T.Route, t, ys), crews, cap), Bool.and(o, y), ok_append(t, ys, crews, cap)),
        L.and_assoc(f, o, y))

law ok_par:
  for +fuel: Nat
  for +size: Nat
  for +routes: RL()
  for +crews: Crews()
  for +cap: Nat
  {P.Routes.ok_par(fuel, size, routes, crews, cap) == P.Routes.ok(routes, crews, cap) : Bool}

law and_both:
  for +a: Bool
  for +b: Bool
  for +c: Bool
  for +d: Bool
  for +ea: {a == c : Bool}
  for +eb: {b == d : Bool}
  {Bool.and(a, b) == Bool.and(c, d) : Bool}

def and_both(a, b, c, d, ea, eb):
  %ea : {Bool.and(a, b) == Bool.and(_, d) : Bool}
  %eb : {Bool.and(a, b) == Bool.and(a, _) : Bool}
  {==}

def ok_par(fuel, size, routes, crews, cap):
  match fuel:
    case 0n:
      {==}
    case 1n+f:
      +half = Nat.div(size, 2n)
      +l = List.take(&2, T.Route, routes, half)
      +r = List.drop(&2, T.Route, routes, half)
      Equal.trans(Bool, Bool.and(P.Routes.ok_par(f, half, l, crews, cap), P.Routes.ok_par(f, Nat.sub(size, half), r, crews, cap)),
        Bool.and(P.Routes.ok(l, crews, cap), P.Routes.ok(r, crews, cap)), P.Routes.ok(routes, crews, cap),
        and_both(P.Routes.ok_par(f, half, l, crews, cap), P.Routes.ok_par(f, Nat.sub(size, half), r, crews, cap), P.Routes.ok(l, crews, cap), P.Routes.ok(r, crews, cap),
          ok_par(f, half, l, crews, cap), ok_par(f, Nat.sub(size, half), r, crews, cap)),
        Equal.trans(Bool, Bool.and(P.Routes.ok(l, crews, cap), P.Routes.ok(r, crews, cap)), P.Routes.ok(List.append(&2, T.Route, l, r), crews, cap), P.Routes.ok(routes, crews, cap),
          Equal.sym(Bool, P.Routes.ok(List.append(&2, T.Route, l, r), crews, cap), Bool.and(P.Routes.ok(l, crews, cap), P.Routes.ok(r, crews, cap)), ok_append(l, r, crews, cap)),
          Equal.cong(RL(), Bool, q => P.Routes.ok(q, crews, cap), List.append(&2, T.Route, l, r), routes, take_drop(T.Route, routes, half))))

law check_valid:
  for +inst: T.Instance
  for +plan: T.Plan
  {P.Plan.check(inst, plan) == P.Plan.valid(inst, plan) : Bool}

def check_valid(inst, plan):
  +routes = T.Plan.routes(plan)
  +crews = T.Instance.crews(inst)
  +cap = T.Instance.cap(inst)
  +size = List.length(&2, T.Route, routes)
  +io = P.Instance.ok(inst)
  +pt = P.Plan.partition_ok(inst, plan)
  +st = P.Slots.sorted(P.Routes.slots(routes))
  Equal.cong(Bool, Bool, b => Bool.and(io, Bool.and(pt, Bool.and(st, b))), P.Routes.ok_par(5n, size, routes, crews, cap), P.Routes.ok(routes, crews, cap), ok_par(5n, size, routes, crews, cap))

# The fallback
# ------------

law count_trivial:
  for +z: T.Appraisal
  for +inst: T.Instance
  {J.count(z, P.Plan.placed(P.Plan.trivial(inst))) == J.count(z, T.Instance.jobs(inst)) : Nat}

def count_trivial(z, inst):
  +j = T.Instance.jobs(inst)
  Equal.trans(Nat, J.count(z, P.Plan.placed(P.Plan.trivial(inst))), Nat.add(J.count(z, j), 0n), J.count(z, j),
    PJ.count_append(z, j, Nil{}), L.add_zero(J.count(z, j)))

law agree_trivial:
  for +zs: AL()
  for +inst: T.Instance
  {PJ.agree(zs, P.Plan.placed(P.Plan.trivial(inst)), T.Instance.jobs(inst)) == True{} : Bool}

def agree_trivial(zs, inst):
  match zs:
    case Nil{}:
      {==}
    case +z <> t:
      +x = P.Plan.placed(P.Plan.trivial(inst))
      +j = T.Instance.jobs(inst)
      L.and_i(Nat.is_eq(J.count(z, x), J.count(z, j)), PJ.agree(t, x, j),
        L.is_eq_of(J.count(z, x), J.count(z, j), count_trivial(z, inst)), agree_trivial(t, inst))

law trivial_valid:
  for +inst: T.Instance
  for +e: {P.Instance.ok(inst) == True{} : Bool}
  {P.Plan.valid(inst, P.Plan.trivial(inst)) == True{} : Bool}

def trivial_valid(inst, e):
  +p = P.Plan.trivial(inst)
  +x = P.Plan.placed(p)
  +j = T.Instance.jobs(inst)
  PP.valid_intro(inst, p, e, PJ.same_sort_intro(x, j, e, agree_trivial(J.sort(x), inst), agree_trivial(j, inst)), {==}, {==})

law publish_go:
  for +c: Bool
  for +inst: T.Instance
  for +plan: T.Plan
  for +eq: {P.Plan.check(inst, plan) == c : Bool}
  for +e: {P.Instance.ok(inst) == True{} : Bool}
  {P.Plan.valid(inst, S.publish.if(c, inst, plan)) == True{} : Bool}

def publish_go(c, inst, plan, eq, e):
  match c:
    case True{}:
      Equal.trans(Bool, P.Plan.valid(inst, plan), P.Plan.check(inst, plan), True{},
        Equal.sym(Bool, P.Plan.check(inst, plan), P.Plan.valid(inst, plan), check_valid(inst, plan)), eq)
    case False{}:
      trivial_valid(inst, e)

law publish_valid:
  for +inst: T.Instance
  for +plan: T.Plan
  for +e: {P.Instance.ok(inst) == True{} : Bool}
  {P.Plan.valid(inst, S.publish(inst, plan)) == True{} : Bool}

def publish_valid(inst, plan, e):
  publish_go(P.Plan.check(inst, plan), inst, plan, {==}, e)

# Improving
# ---------

law keep_score:
  for +c: Bool
  for +inst: T.Instance
  for +plan: T.Plan
  for +next: T.Plan
  for +eq: {S.accepts(inst, plan, next) == c : Bool}
  {Nat.is_le(S.score(S.keep_better(c, plan, next)), S.score(plan)) == True{} : Bool}

def keep_score(c, inst, plan, next, eq):
  match c:
    case True{}:
      L.le_of_lt(S.score(next), S.score(plan),
        L.and_l(Nat.is_lt(S.score(next), S.score(plan)), P.Plan.check(inst, next), eq))
    case False{}:
      L.le_refl(S.score(plan))

law keep_valid:
  for +c: Bool
  for +inst: T.Instance
  for +plan: T.Plan
  for +next: T.Plan
  for +eq: {S.accepts(inst, plan, next) == c : Bool}
  for +ev: {P.Plan.valid(inst, plan) == True{} : Bool}
  {P.Plan.valid(inst, S.keep_better(c, plan, next)) == True{} : Bool}

def keep_valid(c, inst, plan, next, eq, ev):
  match c:
    case True{}:
      Equal.trans(Bool, P.Plan.valid(inst, next), P.Plan.check(inst, next), True{},
        Equal.sym(Bool, P.Plan.check(inst, next), P.Plan.valid(inst, next), check_valid(inst, next)),
        L.and_r(Nat.is_lt(S.score(next), S.score(plan)), P.Plan.check(inst, next), eq))
    case False{}:
      ev

law improve_score:
  for +fuel: Nat
  for +inst: T.Instance
  for +plan: T.Plan
  {Nat.is_le(S.score(S.improve(fuel, inst, plan)), S.score(plan)) == True{} : Bool}

def improve_score(fuel, inst, plan):
  match fuel:
    case 0n:
      L.le_refl(S.score(plan))
    case 1n+f:
      +next = S.pass(T.Instance.cap(inst), plan)
      +c = S.accepts(inst, plan, next)
      +p2 = S.keep_better(c, plan, next)
      L.le_trans(S.score(S.improve(f, inst, p2)), S.score(p2), S.score(plan),
        improve_score(f, inst, p2), keep_score(c, inst, plan, next, {==}))

law improve_valid:
  for +fuel: Nat
  for +inst: T.Instance
  for +plan: T.Plan
  for +ev: {P.Plan.valid(inst, plan) == True{} : Bool}
  {P.Plan.valid(inst, S.improve(fuel, inst, plan)) == True{} : Bool}

def improve_valid(fuel, inst, plan, ev):
  match fuel:
    case 0n:
      ev
    case 1n+f:
      +next = S.pass(T.Instance.cap(inst), plan)
      +c = S.accepts(inst, plan, next)
      improve_valid(f, inst, S.keep_better(c, plan, next), keep_valid(c, inst, plan, next, {==}, ev))

# What the search may consider
# ----------------------------

def NoCand(m: MC()) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      Empty

law none_cand:
  for +x: S.Cand
  for +e: {None{} == Some{x} : MC()}
  Empty

def none_cand(x, e):
  %e : NoCand(_)
  Unit{}

law make_some:
  for +c: Bool
  for +r: T.Route
  for +at: Nat
  for +added: Nat
  for +x: S.Cand
  for +e: {S.Select.make(c, r, at, added) == Some{x} : MC()}
  {c == True{} : Bool}

def make_some(c, r, at, added, x, e):
  match c:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, none_cand(x, e))

def Added(+r: T.Route, +job: T.Appraisal) -> Nat:
  S.Spot.added(S.Select.spot(r, T.Appraisal.site(job)))

def Fits(+r: T.Route, +job: T.Appraisal) -> Bool:
  S.Select.fits(r, job, Added(r, job))

law in_fits:
  for +c: Bool
  for +r: T.Route
  for +job: T.Appraisal
  for +x: S.Cand
  for +e: {S.Select.in(c, r, job) == Some{x} : MC()}
  {Fits(r, job) == True{} : Bool}

def in_fits(c, r, job, x, e):
  match c:
    case False{}:
      Empty.absurd({Fits(r, job) == True{} : Bool}, none_cand(x, e))
    case True{}:
      +s = S.Select.spot(r, T.Appraisal.site(job))
      make_some(Fits(r, job), r, S.Spot.at(s), S.Spot.added(s), x, e)

law out_fits:
  for +c: Bool
  for +cap: Nat
  for +r: T.Route
  for +job: T.Appraisal
  for +x: S.Cand
  for +e: {S.Select.out(c, cap, r, job) == Some{x} : MC()}
  {Fits(r, job) == True{} : Bool}

def out_fits(c, cap, r, job, x, e):
  match c:
    case True{}:
      Empty.absurd({Fits(r, job) == True{} : Bool}, none_cand(x, e))
    case False{}:
      +s = S.Select.spot(r, T.Appraisal.site(job))
      +w = S.Select.within_cap(cap, r, job, S.Spot.at(s))
      L.and_l(Fits(r, job), w, make_some(Bool.and(Fits(r, job), w), r, S.Spot.at(s), S.Spot.added(s), x, e))

law one_fits:
  for +cap: Nat
  for +job: T.Appraisal
  for +outside: Bool
  for +r: T.Route
  for +inzip: Bool
  for +x: S.Cand
  for +e: {S.Select.one.go(cap, job, outside, r, inzip) == Some{x} : MC()}
  {Fits(r, job) == True{} : Bool}

def one_fits(cap, job, outside, r, inzip, x, e):
  match outside:
    case False{}:
      in_fits(inzip, r, job, x, e)
    case True{}:
      out_fits(inzip, cap, r, job, x, e)

law in_zip:
  for +c: Bool
  for +r: T.Route
  for +job: T.Appraisal
  for +x: S.Cand
  for +e: {S.Select.in(c, r, job) == Some{x} : MC()}
  {c == True{} : Bool}

def in_zip(c, r, job, x, e):
  match c:
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, none_cand(x, e))
    case True{}:
      {==}

law wait_tree:
  for +w: S.Work
  for +job: T.Appraisal
  {S.Work.tree(S.Work.wait(w, job)) == S.Work.tree(w) : S.Forest}

def wait_tree(w, job):
  match w:
    case S.Work{t, b, e}:
      {==}

law rescue_stays:
  for +c: Bool
  for +d: Nat
  for +cap: Nat
  for +w: S.Work
  for +job: T.Appraisal
  for +later: {c == False{} : Bool}
  {S.Work.tree(S.place.rescue(c, d, cap, w, job)) == S.Work.tree(w) : S.Forest}

def rescue_stays(c, d, cap, w, job, later):
  match c:
    case True{}:
      L.never({S.Work.tree(S.place.outside(S.Select.tree(S.Work.tree(w), d, cap, job, True{}), cap, w, job)) == S.Work.tree(w) : S.Forest}, Equal.sym(Bool, True{}, False{}, later))
    case False{}:
      wait_tree(w, job)

def Open(+r: T.Route) -> Bool:
  Bool.not(T.Route.closed(r))

def Due(+r: T.Route, +job: T.Appraisal) -> Bool:
  Nat.is_le(T.Route.day(r), T.Appraisal.due(job))

def Hours(+r: T.Route, +job: T.Appraisal) -> Bool:
  Nat.is_le(Nat.add(Nat.add(T.Audit.minutes(T.Route.audit(r)), Added(r, job)), T.Appraisal.minutes(job)), T.Contractor.max_minutes(T.Route.crew(r)))

law fits_open:
  for +r: T.Route
  for +job: T.Appraisal
  for +e: {Fits(r, job) == True{} : Bool}
  {T.Route.closed(r) == False{} : Bool}

def fits_open(r, job, e):
  L.not_t(T.Route.closed(r), L.and_l(Open(r), Bool.and(Due(r, job), Hours(r, job)), e))

law fits_due:
  for +r: T.Route
  for +job: T.Appraisal
  for +e: {Fits(r, job) == True{} : Bool}
  {Due(r, job) == True{} : Bool}

def fits_due(r, job, e):
  L.and_l(Due(r, job), Hours(r, job), L.and_r(Open(r), Bool.and(Due(r, job), Hours(r, job)), e))

law fits_hours:
  for +r: T.Route
  for +job: T.Appraisal
  for +e: {Fits(r, job) == True{} : Bool}
  {Hours(r, job) == True{} : Bool}

def fits_hours(r, job, e):
  L.and_r(Due(r, job), Hours(r, job), L.and_r(Open(r), Bool.and(Due(r, job), Hours(r, job)), e))
