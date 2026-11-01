import Base
import ../core/types.bend as T
import ../core/lifecycle.bend as Life
import ../core/jobs.bend as J
import ../core/route.bend as R
import ./logic.bend as L
import ./jobs.bend as PJ

# Routes: stops as bags, the locked head and open tail, and the theorem healing
# rests on, that every route out of Route.remake is valid.

def ST() -> Data:
  List<&2, T.Stop>

def JC(+a: T.Appraisal, xs: List<&2, T.Stop>) -> Nat:
  J.count(a, R.Stops.jobs(xs))

law ss:
  for -a: ST()
  for -b: ST()
  for e: {a == b : ST()}
  {b == a : ST()}

def ss(a, b, e):
  Equal.sym(ST(), a, b, e)

# Bags of stops
# -------------

law jobs_append:
  for +xs: ST()
  for +ys: ST()
  {R.Stops.jobs(R.Stops.append(xs, ys)) == List.append(&2, T.Appraisal, R.Stops.jobs(xs), R.Stops.jobs(ys)) : List<&2, T.Appraisal>}

def jobs_append(xs, ys):
  match xs:
    case Nil{}:
      {==}
    case s <> r:
      %jobs_append(r, ys) : {T.Stop.job(s) <> R.Stops.jobs(R.Stops.append(r, ys)) == T.Stop.job(s) <> _ : List<&2, T.Appraisal>}
      {==}

law jc_append:
  for +a: T.Appraisal
  for +xs: ST()
  for +ys: ST()
  {JC(a, R.Stops.append(xs, ys)) == Nat.add(JC(a, xs), JC(a, ys)) : Nat}

def jc_append(a, xs, ys):
  Equal.trans(Nat, JC(a, R.Stops.append(xs, ys)),
    J.count(a, List.append(&2, T.Appraisal, R.Stops.jobs(xs), R.Stops.jobs(ys))),
    Nat.add(JC(a, xs), JC(a, ys)),
    Equal.cong(List<&2, T.Appraisal>, Nat, l => J.count(a, l), R.Stops.jobs(R.Stops.append(xs, ys)),
      List.append(&2, T.Appraisal, R.Stops.jobs(xs), R.Stops.jobs(ys)), jobs_append(xs, ys)),
    PJ.count_append(a, R.Stops.jobs(xs), R.Stops.jobs(ys)))

law split_put:
  for +a: T.Appraisal
  for +b: Bool
  for +s: T.Stop
  for +k: ST()
  for +c: ST()
  {Nat.add(JC(a, R.Stops.put(b, s, k)), JC(a, R.Stops.put(Bool.not(b), s, c))) == Nat.add(JC(a, [s]), Nat.add(JC(a, k), JC(a, c))) : Nat}

law jc_one:
  for +a: T.Appraisal
  for +s: T.Stop
  for +k: ST()
  {JC(a, s <> k) == Nat.add(JC(a, [s]), JC(a, k)) : Nat}

def jc_one(a, s, k):
  jc_append(a, [s], k)

def split_put(a, b, s, k, c):
  match b:
    case True{}:
      Equal.trans(Nat, Nat.add(JC(a, s <> k), JC(a, c)), Nat.add(Nat.add(JC(a, [s]), JC(a, k)), JC(a, c)),
        Nat.add(JC(a, [s]), Nat.add(JC(a, k), JC(a, c))),
        L.add_l(JC(a, s <> k), Nat.add(JC(a, [s]), JC(a, k)), JC(a, c), jc_one(a, s, k)),
        L.add_assoc(JC(a, [s]), JC(a, k), JC(a, c)))
    case False{}:
      Equal.trans(Nat, Nat.add(JC(a, k), JC(a, s <> c)), Nat.add(JC(a, k), Nat.add(JC(a, [s]), JC(a, c))),
        Nat.add(JC(a, [s]), Nat.add(JC(a, k), JC(a, c))),
        L.add_r(JC(a, k), JC(a, s <> c), Nat.add(JC(a, [s]), JC(a, c)), jc_one(a, s, c)),
        L.add_swap(JC(a, k), JC(a, [s]), JC(a, c)))

# What keep takes and what cut takes add back up to the whole list.
law jc_split:
  for +a: T.Appraisal
  for +xs: ST()
  for +t: R.Test
  {Nat.add(JC(a, R.Stops.keep(xs, t)), JC(a, R.Stops.cut(xs, t))) == JC(a, xs) : Nat}

def jc_split(a, xs, t):
  match xs:
    case Nil{}:
      {==}
    case +s <> r:
      +b = R.Test.run(t, s)
      +k = R.Stops.keep(r, t)
      +c = R.Stops.cut(r, t)
      Equal.trans(Nat, Nat.add(JC(a, R.Stops.put(b, s, k)), JC(a, R.Stops.put(Bool.not(b), s, c))),
        Nat.add(JC(a, [s]), Nat.add(JC(a, k), JC(a, c))), JC(a, s <> r),
        split_put(a, b, s, k, c),
        Equal.trans(Nat, Nat.add(JC(a, [s]), Nat.add(JC(a, k), JC(a, c))), Nat.add(JC(a, [s]), JC(a, r)), JC(a, s <> r),
          L.add_r(JC(a, [s]), Nat.add(JC(a, k), JC(a, c)), JC(a, r), jc_split(a, r, t)),
          Equal.sym(Nat, JC(a, s <> r), Nat.add(JC(a, [s]), JC(a, r)), jc_one(a, s, r))))

# Head and tail
# -------------

law head_l:
  for +s: T.Stop
  for +r: ST()
  for +e: {R.Stop.locked(s) == True{} : Bool}
  {R.Stops.head(s <> r) == s <> R.Stops.head(r) : ST()}

def head_l(s, r, e):
  %Equal.sym(Bool, R.Stop.locked(s), True{}, e) : {R.Stops.head.put(_, s, R.Stops.head(r)) == s <> R.Stops.head(r) : ST()}
  {==}

law head_o:
  for +s: T.Stop
  for +r: ST()
  for +e: {R.Stop.locked(s) == False{} : Bool}
  {R.Stops.head(s <> r) == Nil{} : ST()}

def head_o(s, r, e):
  %Equal.sym(Bool, R.Stop.locked(s), False{}, e) : {R.Stops.head.put(_, s, R.Stops.head(r)) == Nil{} : ST()}
  {==}

law tail_l:
  for +s: T.Stop
  for +r: ST()
  for +e: {R.Stop.locked(s) == True{} : Bool}
  {R.Stops.tail(s <> r) == R.Stops.tail(r) : ST()}

def tail_l(s, r, e):
  %Equal.sym(Bool, R.Stop.locked(s), True{}, e) : {R.Stops.tail.put(_, s, r, R.Stops.tail(r)) == R.Stops.tail(r) : ST()}
  {==}

law tail_o:
  for +s: T.Stop
  for +r: ST()
  for +e: {R.Stop.locked(s) == False{} : Bool}
  {R.Stops.tail(s <> r) == s <> r : ST()}

def tail_o(s, r, e):
  %Equal.sym(Bool, R.Stop.locked(s), False{}, e) : {R.Stops.tail.put(_, s, r, R.Stops.tail(r)) == s <> r : ST()}
  {==}

law cons_l:
  for +s: T.Stop
  for +r: ST()
  for +e: {R.Stops.append(R.Stops.head(r), R.Stops.tail(r)) == r : ST()}
  {s <> R.Stops.append(R.Stops.head(r), R.Stops.tail(r)) == s <> r : ST()}

def cons_l(s, r, e):
  %e : {s <> R.Stops.append(R.Stops.head(r), R.Stops.tail(r)) == s <> _ : ST()}
  {==}

law split_stops:
  for +xs: ST()
  {R.Stops.append(R.Stops.head(xs), R.Stops.tail(xs)) == xs : ST()}

def split_stops(xs):
  match xs:
    case Nil{}:
      {==}
    case +s <> r:
      L.cases(R.Stop.locked(s), {R.Stops.append(R.Stops.head(s <> r), R.Stops.tail(s <> r)) == s <> r : ST()},
        +e =>
          %ss(R.Stops.head(s <> r), s <> R.Stops.head(r), head_l(s, r, e)) : {R.Stops.append(_, R.Stops.tail(s <> r)) == s <> r : ST()}
          %ss(R.Stops.tail(s <> r), R.Stops.tail(r), tail_l(s, r, e)) : {R.Stops.append(s <> R.Stops.head(r), _) == s <> r : ST()}
          cons_l(s, r, split_stops(r)),
        +e =>
          %ss(R.Stops.head(s <> r), Nil{}, head_o(s, r, e)) : {R.Stops.append(_, R.Stops.tail(s <> r)) == s <> r : ST()}
          tail_o(s, r, e))

law jc_head_tail:
  for +a: T.Appraisal
  for +xs: ST()
  {Nat.add(JC(a, R.Stops.head(xs)), JC(a, R.Stops.tail(xs))) == JC(a, xs) : Nat}

def jc_head_tail(a, xs):
  Equal.trans(Nat, Nat.add(JC(a, R.Stops.head(xs)), JC(a, R.Stops.tail(xs))),
    JC(a, R.Stops.append(R.Stops.head(xs), R.Stops.tail(xs))), JC(a, xs),
    Equal.sym(Nat, JC(a, R.Stops.append(R.Stops.head(xs), R.Stops.tail(xs))),
      Nat.add(JC(a, R.Stops.head(xs)), JC(a, R.Stops.tail(xs))), jc_append(a, R.Stops.head(xs), R.Stops.tail(xs))),
    Equal.cong(ST(), Nat, l => JC(a, l), R.Stops.append(R.Stops.head(xs), R.Stops.tail(xs)), xs, split_stops(xs)))

law locked_head:
  for +xs: ST()
  {R.Stops.all_locked(R.Stops.head(xs)) == True{} : Bool}

def locked_head(xs):
  match xs:
    case Nil{}:
      {==}
    case +s <> r:
      L.cases(R.Stop.locked(s), {R.Stops.all_locked(R.Stops.head(s <> r)) == True{} : Bool},
        +e =>
          %ss(R.Stops.head(s <> r), s <> R.Stops.head(r), head_l(s, r, e)) : {R.Stops.all_locked(_) == True{} : Bool}
          L.and_i(R.Stop.locked(s), R.Stops.all_locked(R.Stops.head(r)), e, locked_head(r)),
        +e =>
          %ss(R.Stops.head(s <> r), Nil{}, head_o(s, r, e)) : {R.Stops.all_locked(_) == True{} : Bool}
          {==})

# An open stop isn't locked.
law open_unlocked:
  for +s: T.Stop
  for +e: {R.Stop.open(s) == True{} : Bool}
  {R.Stop.locked(s) == False{} : Bool}

def open_unlocked(s, e):
  match s:
    case T.Stop{j, T.Open{}}:
      {==}
    case T.Stop{j, T.Underway{}}:
      L.never({True{} == False{} : Bool}, e)
    case T.Stop{j, T.Completed{}}:
      L.never({True{} == False{} : Bool}, e)
    case T.Stop{j, T.Failed{}}:
      {==}
    case T.Stop{j, T.Cancelled{}}:
      {==}

law tail_open:
  for +t: ST()
  for +et: {R.Stops.all_open(t) == True{} : Bool}
  {R.Stops.tail(t) == t : ST()}

def tail_open(t, et):
  match t:
    case Nil{}:
      {==}
    case +s <> r:
      tail_o(s, r, open_unlocked(s, L.and_l(R.Stop.open(s), R.Stops.all_open(r), et)))

law head_open:
  for +t: ST()
  for +et: {R.Stops.all_open(t) == True{} : Bool}
  {R.Stops.head(t) == Nil{} : ST()}

def head_open(t, et):
  match t:
    case Nil{}:
      {==}
    case +s <> r:
      head_o(s, r, open_unlocked(s, L.and_l(R.Stop.open(s), R.Stops.all_open(r), et)))

law head_append:
  for +h: ST()
  for +t: ST()
  for +eh: {R.Stops.all_locked(h) == True{} : Bool}
  for +et: {R.Stops.all_open(t) == True{} : Bool}
  {R.Stops.head(R.Stops.append(h, t)) == h : ST()}

def head_append(h, t, eh, et):
  match h:
    case Nil{}:
      head_open(t, et)
    case +s <> r:
      +rest = R.Stops.append(r, t)
      %ss(R.Stops.head(s <> rest), s <> R.Stops.head(rest), head_l(s, rest, L.and_l(R.Stop.locked(s), R.Stops.all_locked(r), eh))) : {_ == s <> r : ST()}
      %head_append(r, t, L.and_r(R.Stop.locked(s), R.Stops.all_locked(r), eh), et) : {s <> R.Stops.head(rest) == s <> _ : ST()}
      {==}

law tail_append:
  for +h: ST()
  for +t: ST()
  for +eh: {R.Stops.all_locked(h) == True{} : Bool}
  for +et: {R.Stops.all_open(t) == True{} : Bool}
  {R.Stops.tail(R.Stops.append(h, t)) == t : ST()}

def tail_append(h, t, eh, et):
  match h:
    case Nil{}:
      tail_open(t, et)
    case +s <> r:
      +rest = R.Stops.append(r, t)
      %ss(R.Stops.tail(s <> rest), R.Stops.tail(rest), tail_l(s, rest, L.and_l(R.Stop.locked(s), R.Stops.all_locked(r), eh))) : {_ == t : ST()}
      tail_append(r, t, L.and_r(R.Stop.locked(s), R.Stops.all_locked(r), eh), et)

law open_put:
  for +b: Bool
  for +s: T.Stop
  for +k: ST()
  for +es: {R.Stop.open(s) == True{} : Bool}
  for +ek: {R.Stops.all_open(k) == True{} : Bool}
  {R.Stops.all_open(R.Stops.put(b, s, k)) == True{} : Bool}

def open_put(b, s, k, es, ek):
  match b:
    case True{}:
      L.and_i(R.Stop.open(s), R.Stops.all_open(k), es, ek)
    case False{}:
      ek

law open_keep:
  for +xs: ST()
  for +t: R.Test
  for +e: {R.Stops.all_open(xs) == True{} : Bool}
  {R.Stops.all_open(R.Stops.keep(xs, t)) == True{} : Bool}

def open_keep(xs, t, e):
  match xs:
    case Nil{}:
      {==}
    case +s <> r:
      open_put(R.Test.run(t, s), s, R.Stops.keep(r, t), L.and_l(R.Stop.open(s), R.Stops.all_open(r), e),
        open_keep(r, t, L.and_r(R.Stop.open(s), R.Stops.all_open(r), e)))

law open_cut:
  for +xs: ST()
  for +t: R.Test
  for +e: {R.Stops.all_open(xs) == True{} : Bool}
  {R.Stops.all_open(R.Stops.cut(xs, t)) == True{} : Bool}

def open_cut(xs, t, e):
  match xs:
    case Nil{}:
      {==}
    case +s <> r:
      open_put(Bool.not(R.Test.run(t, s)), s, R.Stops.cut(r, t), L.and_l(R.Stop.open(s), R.Stops.all_open(r), e),
        open_cut(r, t, L.and_r(R.Stop.open(s), R.Stops.all_open(r), e)))

law locked_put:
  for +b: Bool
  for +s: T.Stop
  for +k: ST()
  for +es: {R.Stop.locked(s) == True{} : Bool}
  for +ek: {R.Stops.all_locked(k) == True{} : Bool}
  {R.Stops.all_locked(R.Stops.put(b, s, k)) == True{} : Bool}

def locked_put(b, s, k, es, ek):
  match b:
    case True{}:
      L.and_i(R.Stop.locked(s), R.Stops.all_locked(k), es, ek)
    case False{}:
      ek

law locked_cut:
  for +xs: ST()
  for +t: R.Test
  for +e: {R.Stops.all_locked(xs) == True{} : Bool}
  {R.Stops.all_locked(R.Stops.cut(xs, t)) == True{} : Bool}

def locked_cut(xs, t, e):
  match xs:
    case Nil{}:
      {==}
    case +s <> r:
      locked_put(Bool.not(R.Test.run(t, s)), s, R.Stops.cut(r, t), L.and_l(R.Stop.locked(s), R.Stops.all_locked(r), e),
        locked_cut(r, t, L.and_r(R.Stop.locked(s), R.Stops.all_locked(r), e)))

law locked_append:
  for +xs: ST()
  for +ys: ST()
  for +ex: {R.Stops.all_locked(xs) == True{} : Bool}
  for +ey: {R.Stops.all_locked(ys) == True{} : Bool}
  {R.Stops.all_locked(R.Stops.append(xs, ys)) == True{} : Bool}

def locked_append(xs, ys, ex, ey):
  match xs:
    case Nil{}:
      ey
    case +s <> r:
      L.and_i(R.Stop.locked(s), R.Stops.all_locked(R.Stops.append(r, ys)),
        L.and_l(R.Stop.locked(s), R.Stops.all_locked(r), ex),
        locked_append(r, ys, L.and_r(R.Stop.locked(s), R.Stops.all_locked(r), ex), ey))

# Keeping twice keeps the same stops.
law keep_put:
  for +t: R.Test
  for +s: T.Stop
  for +k: ST()
  for +b: Bool
  for +e: {R.Test.run(t, s) == b : Bool}
  for +ih: {R.Stops.keep(k, t) == k : ST()}
  {R.Stops.keep(R.Stops.put(b, s, k), t) == R.Stops.put(b, s, k) : ST()}

def keep_put(t, s, k, b, e, ih):
  match b:
    case True{}:
      %Equal.sym(Bool, R.Test.run(t, s), True{}, e) : {R.Stops.put(_, s, R.Stops.keep(k, t)) == s <> k : ST()}
      %ih : {s <> R.Stops.keep(k, t) == s <> _ : ST()}
      {==}
    case False{}:
      ih

law keep_idem:
  for +xs: ST()
  for +t: R.Test
  {R.Stops.keep(R.Stops.keep(xs, t), t) == R.Stops.keep(xs, t) : ST()}

def keep_idem(xs, t):
  match xs:
    case Nil{}:
      {==}
    case +s <> r:
      keep_put(t, s, R.Stops.keep(r, t), R.Test.run(t, s), {==}, keep_idem(r, t))

# Sealed routes
# -------------

law audit_refl:
  for +a: T.Audit
  {T.Audit.is_eq(a, a) == True{} : Bool}

def audit_refl(a):
  match a:
    case T.Audit{m, x, o, f, l, u}:
      +r1 = Bool.and(Nat.is_eq(x, x), Bool.and(T.Bool.is_eq(o, o), Bool.and(T.Bool.is_eq(f, f), Bool.and(T.Nats.is_eq(l, l), T.Nats.is_eq(u, u)))))
      +r2 = Bool.and(T.Bool.is_eq(o, o), Bool.and(T.Bool.is_eq(f, f), Bool.and(T.Nats.is_eq(l, l), T.Nats.is_eq(u, u))))
      +r3 = Bool.and(T.Bool.is_eq(f, f), Bool.and(T.Nats.is_eq(l, l), T.Nats.is_eq(u, u)))
      +r4 = Bool.and(T.Nats.is_eq(l, l), T.Nats.is_eq(u, u))
      L.and_i(Nat.is_eq(m, m), r1, L.eq_refl(m),
        L.and_i(Nat.is_eq(x, x), r2, L.eq_refl(x),
          L.and_i(T.Bool.is_eq(o, o), r3, L.bool_refl(o),
            L.and_i(T.Bool.is_eq(f, f), r4, L.bool_refl(f),
              L.and_i(T.Nats.is_eq(l, l), T.Nats.is_eq(u, u), L.nats_refl(l), L.nats_refl(u))))))

law ok_seal:
  for +cap: Nat
  for +crew: T.Contractor
  for +day: Nat
  for +stops: ST()
  for +closed: Bool
  for +e1: {R.Stops.all_open(R.Stops.tail(stops)) == True{} : Bool}
  for +e2: {Nat.is_le(R.Route.extra(crew, stops), cap) == True{} : Bool}
  {R.Route.ok(cap, R.Route.seal(crew, day, stops, closed)) == True{} : Bool}

def ok_seal(cap, crew, day, stops, closed, e1, e2):
  +a = R.Audit.of(crew, day, stops)
  L.and_i(R.Stops.all_open(R.Stops.tail(stops)), Bool.and(T.Audit.is_eq(a, a), Nat.is_le(T.Audit.extra(a), cap)), e1,
    L.and_i(T.Audit.is_eq(a, a), Nat.is_le(T.Audit.extra(a), cap), audit_refl(a), e2))

law remake_t:
  for +cap: Nat
  for +crew: T.Contractor
  for +day: Nat
  for +closed: Bool
  for +h: ST()
  for +t: ST()
  for +e: {Nat.is_le(R.Route.extra(crew, R.Stops.append(h, t)), cap) == True{} : Bool}
  {R.Route.remake(cap, crew, day, closed, h, t) == R.Step{R.Route.seal(crew, day, R.Stops.append(h, t), closed), Nil{}} : R.Step}

def remake_t(cap, crew, day, closed, h, t, e):
  %Equal.sym(Bool, Nat.is_le(R.Route.extra(crew, R.Stops.append(h, t)), cap), True{}, e) : {R.Route.remake.if(_, crew, day, closed, h, t) == R.Step{R.Route.seal(crew, day, R.Stops.append(h, t), closed), Nil{}} : R.Step}
  {==}

def Trim(+crew: T.Contractor, +h: ST(), +t: ST()) -> ST():
  R.Stops.append(h, R.Stops.keep(t, R.Crew.inside(crew)))

law remake_f:
  for +cap: Nat
  for +crew: T.Contractor
  for +day: Nat
  for +closed: Bool
  for +h: ST()
  for +t: ST()
  for +e: {Nat.is_le(R.Route.extra(crew, R.Stops.append(h, t)), cap) == False{} : Bool}
  {R.Route.remake(cap, crew, day, closed, h, t) == R.Step{R.Route.seal(crew, day, Trim(crew, h, t), closed), R.Stops.cut(t, R.Crew.inside(crew))} : R.Step}

def remake_f(cap, crew, day, closed, h, t, e):
  %Equal.sym(Bool, Nat.is_le(R.Route.extra(crew, R.Stops.append(h, t)), cap), False{}, e) : {R.Route.remake.if(_, crew, day, closed, h, t) == R.Step{R.Route.seal(crew, day, Trim(crew, h, t), closed), R.Stops.cut(t, R.Crew.inside(crew))} : R.Step}
  {==}

# After shedding there's nothing left to charge the cap.
law trim_again:
  for +crew: T.Contractor
  for +h: ST()
  for +t: ST()
  for +eh: {R.Stops.all_locked(h) == True{} : Bool}
  for +et: {R.Stops.all_open(t) == True{} : Bool}
  {R.Stops.append(R.Stops.head(Trim(crew, h, t)), R.Stops.keep(R.Stops.tail(Trim(crew, h, t)), R.Crew.inside(crew))) == Trim(crew, h, t) : ST()}

def trim_again(crew, h, t, eh, et):
  +z = R.Crew.inside(crew)
  +k = R.Stops.keep(t, z)
  +ek = open_keep(t, z, et)
  %ss(R.Stops.head(R.Stops.append(h, k)), h, head_append(h, k, eh, ek)) : {R.Stops.append(_, R.Stops.keep(R.Stops.tail(R.Stops.append(h, k)), z)) == R.Stops.append(h, k) : ST()}
  %ss(R.Stops.tail(R.Stops.append(h, k)), k, tail_append(h, k, eh, ek)) : {R.Stops.append(h, R.Stops.keep(_, z)) == R.Stops.append(h, k) : ST()}
  %ss(R.Stops.keep(k, z), k, keep_idem(t, z)) : {R.Stops.append(h, _) == R.Stops.append(h, k) : ST()}
  {==}

law extra_trim:
  for +crew: T.Contractor
  for +h: ST()
  for +t: ST()
  for +eh: {R.Stops.all_locked(h) == True{} : Bool}
  for +et: {R.Stops.all_open(t) == True{} : Bool}
  {R.Route.extra(crew, Trim(crew, h, t)) == 0n : Nat}

def extra_trim(crew, h, t, eh, et):
  +s2 = Trim(crew, h, t)
  +z = R.Crew.inside(crew)
  +inner = R.Stops.append(R.Stops.head(s2), R.Stops.keep(R.Stops.tail(s2), z))
  Equal.trans(Nat, Nat.sub(R.Route.loop_drive(crew, s2), R.Route.loop_drive(crew, inner)),
    Nat.sub(R.Route.loop_drive(crew, s2), R.Route.loop_drive(crew, s2)), 0n,
    Equal.cong(ST(), Nat, l => Nat.sub(R.Route.loop_drive(crew, s2), R.Route.loop_drive(crew, l)), inner, s2, trim_again(crew, h, t, eh, et)),
    L.sub_self(R.Route.loop_drive(crew, s2)))

law le_of_zero:
  for -a: Nat
  for +b: Nat
  for e: {a == 0n : Nat}
  {Nat.is_le(a, b) == True{} : Bool}

def le_of_zero(a, b, e):
  %Equal.sym(Nat, a, 0n, e) : {Nat.is_le(_, b) == True{} : Bool}
  L.le_zero(b)

law open_tail_full:
  for +h: ST()
  for +t: ST()
  for +eh: {R.Stops.all_locked(h) == True{} : Bool}
  for +et: {R.Stops.all_open(t) == True{} : Bool}
  {R.Stops.all_open(R.Stops.tail(R.Stops.append(h, t))) == True{} : Bool}

def open_tail_full(h, t, eh, et):
  %ss(R.Stops.tail(R.Stops.append(h, t)), t, tail_append(h, t, eh, et)) : {R.Stops.all_open(_) == True{} : Bool}
  et

# Every route out of remake is valid, whatever the head and tail hold, as long as
# the head is locked and the tail is open.
law ok_remake:
  for +cap: Nat
  for +crew: T.Contractor
  for +day: Nat
  for +closed: Bool
  for +h: ST()
  for +t: ST()
  for +eh: {R.Stops.all_locked(h) == True{} : Bool}
  for +et: {R.Stops.all_open(t) == True{} : Bool}
  {R.Route.ok(cap, R.Step.route(R.Route.remake(cap, crew, day, closed, h, t))) == True{} : Bool}

def ok_remake(cap, crew, day, closed, h, t, eh, et):
  +full = R.Stops.append(h, t)
  +m = R.Route.remake(cap, crew, day, closed, h, t)
  +z = R.Crew.inside(crew)
  L.cases(Nat.is_le(R.Route.extra(crew, full), cap), {R.Route.ok(cap, R.Step.route(m)) == True{} : Bool},
    +e =>
      %Equal.sym(R.Step, m, R.Step{R.Route.seal(crew, day, full, closed), Nil{}}, remake_t(cap, crew, day, closed, h, t, e)) : {R.Route.ok(cap, R.Step.route(_)) == True{} : Bool}
      ok_seal(cap, crew, day, full, closed, open_tail_full(h, t, eh, et), e),
    +e =>
      %Equal.sym(R.Step, m, R.Step{R.Route.seal(crew, day, Trim(crew, h, t), closed), R.Stops.cut(t, z)}, remake_f(cap, crew, day, closed, h, t, e)) : {R.Route.ok(cap, R.Step.route(_)) == True{} : Bool}
      ok_seal(cap, crew, day, Trim(crew, h, t), closed,
        open_tail_full(h, R.Stops.keep(t, z), eh, open_keep(t, z, et)),
        le_of_zero(R.Route.extra(crew, Trim(crew, h, t)), cap, extra_trim(crew, h, t, eh, et))))

# Nothing goes missing in a remake: what's on the route plus what was shed.
law jc_remake:
  for +a: T.Appraisal
  for +cap: Nat
  for +crew: T.Contractor
  for +day: Nat
  for +closed: Bool
  for +h: ST()
  for +t: ST()
  {Nat.add(JC(a, T.Route.stops(R.Step.route(R.Route.remake(cap, crew, day, closed, h, t)))), JC(a, R.Step.shed(R.Route.remake(cap, crew, day, closed, h, t)))) == Nat.add(JC(a, h), JC(a, t)) : Nat}

def jc_remake(a, cap, crew, day, closed, h, t):
  +full = R.Stops.append(h, t)
  +m = R.Route.remake(cap, crew, day, closed, h, t)
  +z = R.Crew.inside(crew)
  L.cases(Nat.is_le(R.Route.extra(crew, full), cap), {Nat.add(JC(a, T.Route.stops(R.Step.route(m))), JC(a, R.Step.shed(m))) == Nat.add(JC(a, h), JC(a, t)) : Nat},
    +e =>
      %Equal.sym(R.Step, m, R.Step{R.Route.seal(crew, day, full, closed), Nil{}}, remake_t(cap, crew, day, closed, h, t, e)) : {Nat.add(JC(a, T.Route.stops(R.Step.route(_))), JC(a, R.Step.shed(_))) == Nat.add(JC(a, h), JC(a, t)) : Nat}
      Equal.trans(Nat, Nat.add(JC(a, full), 0n), JC(a, full), Nat.add(JC(a, h), JC(a, t)), L.add_zero(JC(a, full)), jc_append(a, h, t)),
    +e =>
      %Equal.sym(R.Step, m, R.Step{R.Route.seal(crew, day, Trim(crew, h, t), closed), R.Stops.cut(t, z)}, remake_f(cap, crew, day, closed, h, t, e)) : {Nat.add(JC(a, T.Route.stops(R.Step.route(_))), JC(a, R.Step.shed(_))) == Nat.add(JC(a, h), JC(a, t)) : Nat}
      +k = R.Stops.keep(t, z)
      +c = R.Stops.cut(t, z)
      Equal.trans(Nat, Nat.add(JC(a, R.Stops.append(h, k)), JC(a, c)), Nat.add(Nat.add(JC(a, h), JC(a, k)), JC(a, c)),
        Nat.add(JC(a, h), JC(a, t)),
        L.add_l(JC(a, R.Stops.append(h, k)), Nat.add(JC(a, h), JC(a, k)), JC(a, c), jc_append(a, h, k)),
        Equal.trans(Nat, Nat.add(Nat.add(JC(a, h), JC(a, k)), JC(a, c)), Nat.add(JC(a, h), Nat.add(JC(a, k), JC(a, c))),
          Nat.add(JC(a, h), JC(a, t)),
          L.add_assoc(JC(a, h), JC(a, k), JC(a, c)),
          L.add_r(JC(a, h), Nat.add(JC(a, k), JC(a, c)), JC(a, t), jc_split(a, t, z)))))

# The crew and day don't change in a remake.
law crew_remake:
  for +cap: Nat
  for +crew: T.Contractor
  for +day: Nat
  for +closed: Bool
  for +h: ST()
  for +t: ST()
  {T.Route.crew(R.Step.route(R.Route.remake(cap, crew, day, closed, h, t))) == crew : T.Contractor}

def crew_remake(cap, crew, day, closed, h, t):
  +full = R.Stops.append(h, t)
  +m = R.Route.remake(cap, crew, day, closed, h, t)
  +z = R.Crew.inside(crew)
  L.cases(Nat.is_le(R.Route.extra(crew, full), cap), {T.Route.crew(R.Step.route(m)) == crew : T.Contractor},
    +e =>
      %Equal.sym(R.Step, m, R.Step{R.Route.seal(crew, day, full, closed), Nil{}}, remake_t(cap, crew, day, closed, h, t, e)) : {T.Route.crew(R.Step.route(_)) == crew : T.Contractor}
      {==},
    +e =>
      %Equal.sym(R.Step, m, R.Step{R.Route.seal(crew, day, Trim(crew, h, t), closed), R.Stops.cut(t, z)}, remake_f(cap, crew, day, closed, h, t, e)) : {T.Route.crew(R.Step.route(_)) == crew : T.Contractor}
      {==})

law day_remake:
  for +cap: Nat
  for +crew: T.Contractor
  for +day: Nat
  for +closed: Bool
  for +h: ST()
  for +t: ST()
  {T.Route.day(R.Step.route(R.Route.remake(cap, crew, day, closed, h, t))) == day : Nat}

def day_remake(cap, crew, day, closed, h, t):
  +full = R.Stops.append(h, t)
  +m = R.Route.remake(cap, crew, day, closed, h, t)
  +z = R.Crew.inside(crew)
  L.cases(Nat.is_le(R.Route.extra(crew, full), cap), {T.Route.day(R.Step.route(m)) == day : Nat},
    +e =>
      %Equal.sym(R.Step, m, R.Step{R.Route.seal(crew, day, full, closed), Nil{}}, remake_t(cap, crew, day, closed, h, t, e)) : {T.Route.day(R.Step.route(_)) == day : Nat}
      {==},
    +e =>
      %Equal.sym(R.Step, m, R.Step{R.Route.seal(crew, day, Trim(crew, h, t), closed), R.Stops.cut(t, z)}, remake_f(cap, crew, day, closed, h, t, e)) : {T.Route.day(R.Step.route(_)) == day : Nat}
      {==})

# Locked stops
# ------------

law locked_open:
  for +t: ST()
  for +et: {R.Stops.all_open(t) == True{} : Bool}
  {R.Stops.locked(t) == Nil{} : ST()}

law put_f:
  for +s: T.Stop
  for +r: ST()
  for +e: {R.Stop.locked(s) == False{} : Bool}
  {R.Stops.locked(s <> r) == R.Stops.locked(r) : ST()}

def put_f(s, r, e):
  %Equal.sym(Bool, R.Stop.locked(s), False{}, e) : {R.Stops.put(_, s, R.Stops.locked(r)) == R.Stops.locked(r) : ST()}
  {==}

law put_t:
  for +s: T.Stop
  for +r: ST()
  for +e: {R.Stop.locked(s) == True{} : Bool}
  {R.Stops.locked(s <> r) == s <> R.Stops.locked(r) : ST()}

def put_t(s, r, e):
  %Equal.sym(Bool, R.Stop.locked(s), True{}, e) : {R.Stops.put(_, s, R.Stops.locked(r)) == s <> R.Stops.locked(r) : ST()}
  {==}

def locked_open(t, et):
  match t:
    case Nil{}:
      {==}
    case +s <> r:
      %ss(R.Stops.locked(s <> r), R.Stops.locked(r), put_f(s, r, open_unlocked(s, L.and_l(R.Stop.open(s), R.Stops.all_open(r), et)))) : {_ == Nil{} : ST()}
      locked_open(r, L.and_r(R.Stop.open(s), R.Stops.all_open(r), et))

law locked_app:
  for +h: ST()
  for +t: ST()
  for +eh: {R.Stops.all_locked(h) == True{} : Bool}
  for +et: {R.Stops.all_open(t) == True{} : Bool}
  {R.Stops.locked(R.Stops.append(h, t)) == h : ST()}

def locked_app(h, t, eh, et):
  match h:
    case Nil{}:
      locked_open(t, et)
    case +s <> r:
      +rest = R.Stops.append(r, t)
      %ss(R.Stops.locked(s <> rest), s <> R.Stops.locked(rest), put_t(s, rest, L.and_l(R.Stop.locked(s), R.Stops.all_locked(r), eh))) : {_ == s <> r : ST()}
      %locked_app(r, t, L.and_r(R.Stop.locked(s), R.Stops.all_locked(r), eh), et) : {s <> R.Stops.locked(rest) == s <> _ : ST()}
      {==}

law locked_remake:
  for +cap: Nat
  for +crew: T.Contractor
  for +day: Nat
  for +closed: Bool
  for +h: ST()
  for +t: ST()
  for +eh: {R.Stops.all_locked(h) == True{} : Bool}
  for +et: {R.Stops.all_open(t) == True{} : Bool}
  {R.Stops.locked(T.Route.stops(R.Step.route(R.Route.remake(cap, crew, day, closed, h, t)))) == h : ST()}

def locked_remake(cap, crew, day, closed, h, t, eh, et):
  +full = R.Stops.append(h, t)
  +m = R.Route.remake(cap, crew, day, closed, h, t)
  +z = R.Crew.inside(crew)
  L.cases(Nat.is_le(R.Route.extra(crew, full), cap), {R.Stops.locked(T.Route.stops(R.Step.route(m))) == h : ST()},
    +e =>
      %Equal.sym(R.Step, m, R.Step{R.Route.seal(crew, day, full, closed), Nil{}}, remake_t(cap, crew, day, closed, h, t, e)) : {R.Stops.locked(T.Route.stops(R.Step.route(_))) == h : ST()}
      locked_app(h, t, eh, et),
    +e =>
      %Equal.sym(R.Step, m, R.Step{R.Route.seal(crew, day, Trim(crew, h, t), closed), R.Stops.cut(t, z)}, remake_f(cap, crew, day, closed, h, t, e)) : {R.Stops.locked(T.Route.stops(R.Step.route(_))) == h : ST()}
      locked_app(h, R.Stops.keep(t, z), eh, open_keep(t, z, et)))

# A route's locked stops are its head once the tail is open.
law locked_is_head:
  for +xs: ST()
  for +et: {R.Stops.all_open(R.Stops.tail(xs)) == True{} : Bool}
  {R.Stops.locked(xs) == R.Stops.head(xs) : ST()}

def locked_is_head(xs, et):
  +h = R.Stops.head(xs)
  +t = R.Stops.tail(xs)
  Equal.trans(ST(), R.Stops.locked(xs), R.Stops.locked(R.Stops.append(h, t)), h,
    Equal.cong(ST(), ST(), l => R.Stops.locked(l), xs, R.Stops.append(h, t), ss(R.Stops.append(h, t), xs, split_stops(xs))),
    locked_app(h, t, locked_head(xs), et))
