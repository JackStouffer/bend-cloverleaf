import Base
import ../core/types.bend as T

# Lemmas Base doesn't have. Bool tests and Nat order are the working language of
# every proof here, because laws state checks as {f(x) == True{} : Bool}.

def Disc(b: Bool) -> Type:
  match b:
    case True{}:
      Empty
    case False{}:
      Unit

law ff:
  for e: {False{} == True{} : Bool}
  Empty

def ff(e):
  %e : Disc(_)
  Unit{}

law never:
  for -A: Type
  for e: {False{} == True{} : Bool}
  A

def never(A, e):
  Empty.absurd(A, ff(e))

law cases:
  for +b: Bool
  for -A: Type
  for t: {b == True{} : Bool} -> A
  for f: {b == False{} : Bool} -> A
  A

def cases(b, A, t, f):
  match b:
    case True{}:
      t({==})
    case False{}:
      f({==})

law clash:
  for -b: Bool
  for -A: Type
  for t: {b == True{} : Bool}
  for f: {b == False{} : Bool}
  A

def clash(b, A, t, f):
  never(A, Equal.trans(Bool, False{}, b, True{}, Equal.sym(Bool, b, False{}, f), t))

law and_l:
  for +a: Bool
  for -b: Bool
  for e: {Bool.and(a, b) == True{} : Bool}
  {a == True{} : Bool}

def and_l(a, b, e):
  match a:
    case True{}:
      {==}
    case False{}:
      e

law and_r:
  for +a: Bool
  for -b: Bool
  for e: {Bool.and(a, b) == True{} : Bool}
  {b == True{} : Bool}

def and_r(a, b, e):
  match a:
    case True{}:
      e
    case False{}:
      never({b == True{} : Bool}, e)

law and_i:
  for +a: Bool
  for -b: Bool
  for ea: {a == True{} : Bool}
  for eb: {b == True{} : Bool}
  {Bool.and(a, b) == True{} : Bool}

def and_i(a, b, ea, eb):
  match a:
    case True{}:
      eb
    case False{}:
      ea

law not_true:
  for +b: Bool
  for e: {Bool.not(b) == False{} : Bool}
  {b == True{} : Bool}

def not_true(b, e):
  match b:
    case True{}:
      {==}
    case False{}:
      Equal.sym(Bool, True{}, False{}, e)

# Nat order
# ---------

law eq_refl:
  for +a: Nat
  {Nat.is_eq(a, a) == True{} : Bool}

def eq_refl(a):
  match a:
    case 0n:
      {==}
    case 1n+p:
      eq_refl(p)

law succ_cong:
  for -a: Nat
  for -b: Nat
  for e: {a == b : Nat}
  {1n+a == 1n+b : Nat}

def succ_cong(a, b, e):
  %e : {1n+a == 1n+_ : Nat}
  {==}

law eq_of:
  for +a: Nat
  for +b: Nat
  for e: {Nat.is_eq(a, b) == True{} : Bool}
  {a == b : Nat}

def eq_of(a, b, e):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      never({0n == 1n+q : Nat}, e)
    case 1n+p 0n:
      never({1n+p == 0n : Nat}, e)
    case 1n+p 1n+q:
      succ_cong(p, q, eq_of(p, q, e))

law le_refl:
  for +a: Nat
  {Nat.is_le(a, a) == True{} : Bool}

def le_refl(a):
  match a:
    case 0n:
      {==}
    case 1n+p:
      le_refl(p)

law le_zero:
  for +a: Nat
  {Nat.is_le(0n, a) == True{} : Bool}

def le_zero(a):
  match a:
    case 0n:
      {==}
    case 1n+p:
      {==}

law le_trans:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for ab: {Nat.is_le(a, b) == True{} : Bool}
  for bc: {Nat.is_le(b, c) == True{} : Bool}
  {Nat.is_le(a, c) == True{} : Bool}

def le_trans(a, b, c, ab, bc):
  match a b c:
    case 0n _ 0n:
      {==}
    case 0n _ 1n+cp:
      {==}
    case 1n+ap 0n 0n:
      never({False{} == True{} : Bool}, ab)
    case 1n+ap 0n 1n+cp:
      never({Nat.is_le(ap, cp) == True{} : Bool}, ab)
    case 1n+ap 1n+bp 0n:
      never({False{} == True{} : Bool}, bc)
    case 1n+ap 1n+bp 1n+cp:
      le_trans(ap, bp, cp, ab, bc)

law le_step:
  for +a: Nat
  {Nat.is_le(a, 1n+a) == True{} : Bool}

def le_step(a):
  match a:
    case 0n:
      {==}
    case 1n+p:
      le_step(p)

# From a+1 <= b, a <= b.
law le_weak:
  for +a: Nat
  for +b: Nat
  for e: {Nat.is_le(1n+a, b) == True{} : Bool}
  {Nat.is_le(a, b) == True{} : Bool}

def le_weak(a, b, e):
  le_trans(a, 1n+a, b, le_step(a), e)

law le_total:
  for +a: Nat
  for +b: Nat
  for e: {Nat.is_le(a, b) == False{} : Bool}
  {Nat.is_le(1n+b, a) == True{} : Bool}

def le_total(a, b, e):
  match a b:
    case 0n 0n:
      never({Nat.is_le(1n, 0n) == True{} : Bool}, Equal.sym(Bool, True{}, False{}, e))
    case 0n 1n+q:
      never({Nat.is_le(2n+q, 0n) == True{} : Bool}, Equal.sym(Bool, True{}, False{}, e))
    case 1n+p 0n:
      le_zero(p)
    case 1n+p 1n+q:
      le_total(p, q, e)

law le_antisym:
  for +a: Nat
  for +b: Nat
  for ab: {Nat.is_le(a, b) == True{} : Bool}
  for ba: {Nat.is_le(b, a) == True{} : Bool}
  {a == b : Nat}

def le_antisym(a, b, ab, ba):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      never({0n == 1n+q : Nat}, ba)
    case 1n+p 0n:
      never({1n+p == 0n : Nat}, ab)
    case 1n+p 1n+q:
      succ_cong(p, q, le_antisym(p, q, ab, ba))

# Strict below is never reflexive.
law lt_irrefl:
  for +a: Nat
  for e: {Nat.is_le(1n+a, a) == True{} : Bool}
  Empty

def lt_irrefl(a, e):
  match a:
    case 0n:
      ff(e)
    case 1n+p:
      lt_irrefl(p, e)

# Nat addition
# ------------

law add_zero:
  for +a: Nat
  {Nat.add(a, 0n) == a : Nat}

def add_zero(a):
  match a:
    case 0n:
      {==}
    case 1n+p:
      succ_cong(Nat.add(p, 0n), p, add_zero(p))

law add_succ:
  for +a: Nat
  for -b: Nat
  {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}

def add_succ(a, b):
  match a:
    case 0n:
      {==}
    case 1n+p:
      succ_cong(Nat.add(p, 1n+b), 1n+Nat.add(p, b), add_succ(p, b))

law add_comm:
  for +a: Nat
  for +b: Nat
  {Nat.add(a, b) == Nat.add(b, a) : Nat}

def add_comm(a, b):
  match a:
    case 0n:
      Equal.sym(Nat, Nat.add(b, 0n), b, add_zero(b))
    case 1n+p:
      Equal.trans(Nat, 1n+Nat.add(p, b), 1n+Nat.add(b, p), Nat.add(b, 1n+p),
        succ_cong(Nat.add(p, b), Nat.add(b, p), add_comm(p, b)),
        Equal.sym(Nat, Nat.add(b, 1n+p), 1n+Nat.add(b, p), add_succ(b, p)))

law add_assoc:
  for +a: Nat
  for -b: Nat
  for -c: Nat
  {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}

def add_assoc(a, b, c):
  match a:
    case 0n:
      {==}
    case 1n+p:
      succ_cong(Nat.add(Nat.add(p, b), c), Nat.add(p, Nat.add(b, c)), add_assoc(p, b, c))

# Cancelling on the left turns a count equation on x<>xs into one on xs.
law add_cancel:
  for +a: Nat
  for -b: Nat
  for -c: Nat
  for e: {Nat.add(a, b) == Nat.add(a, c) : Nat}
  {b == c : Nat}

def Pred(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

def add_cancel(a, b, c, e):
  match a:
    case 0n:
      e
    case 1n+p:
      add_cancel(p, b, c, Equal.cong(Nat, Nat, Pred, 1n+Nat.add(p, b), 1n+Nat.add(p, c), e))

law add_swap:
  for +a: Nat
  for +b: Nat
  for -c: Nat
  {Nat.add(a, Nat.add(b, c)) == Nat.add(b, Nat.add(a, c)) : Nat}

def add_swap(a, b, c):
  Equal.trans(Nat, Nat.add(a, Nat.add(b, c)), Nat.add(Nat.add(a, b), c), Nat.add(b, Nat.add(a, c)),
    Equal.sym(Nat, Nat.add(Nat.add(a, b), c), Nat.add(a, Nat.add(b, c)), add_assoc(a, b, c)),
    Equal.trans(Nat, Nat.add(Nat.add(a, b), c), Nat.add(Nat.add(b, a), c), Nat.add(b, Nat.add(a, c)),
      Equal.cong(Nat, Nat, x => Nat.add(x, c), Nat.add(a, b), Nat.add(b, a), add_comm(a, b)),
      add_assoc(b, a, c)))

law add_r:
  for -o: Nat
  for -x: Nat
  for -y: Nat
  for e: {x == y : Nat}
  {Nat.add(o, x) == Nat.add(o, y) : Nat}

def add_r(o, x, y, e):
  %e : {Nat.add(o, x) == Nat.add(o, _) : Nat}
  {==}

law add_l:
  for -x: Nat
  for -y: Nat
  for -o: Nat
  for e: {x == y : Nat}
  {Nat.add(x, o) == Nat.add(y, o) : Nat}

def add_l(x, y, o, e):
  %e : {Nat.add(x, o) == Nat.add(_, o) : Nat}
  {==}

# o + m == (o + s) + c, from m == s + c.
law assoc_step:
  for +o: Nat
  for -m: Nat
  for -s: Nat
  for -c: Nat
  for ih: {m == Nat.add(s, c) : Nat}
  {Nat.add(o, m) == Nat.add(Nat.add(o, s), c) : Nat}

def assoc_step(o, m, s, c, ih):
  Equal.trans(Nat, Nat.add(o, m), Nat.add(o, Nat.add(s, c)), Nat.add(Nat.add(o, s), c),
    add_r(o, m, Nat.add(s, c), ih),
    Equal.sym(Nat, Nat.add(Nat.add(o, s), c), Nat.add(o, Nat.add(s, c)), add_assoc(o, s, c)))

# o + m == x + (o + c), from m == x + c.
law swap_step:
  for +o: Nat
  for -m: Nat
  for +x: Nat
  for -c: Nat
  for ih: {m == Nat.add(x, c) : Nat}
  {Nat.add(o, m) == Nat.add(x, Nat.add(o, c)) : Nat}

def swap_step(o, m, x, c, ih):
  Equal.trans(Nat, Nat.add(o, m), Nat.add(o, Nat.add(x, c)), Nat.add(x, Nat.add(o, c)),
    add_r(o, m, Nat.add(x, c), ih), add_swap(o, x, c))

# (x + (v + r) + l) with the summands reshuffled, which is what swapping a Braun
# tree's children does to a count.
law shuffle:
  for +x: Nat
  for +v: Nat
  for +r: Nat
  for +l: Nat
  {Nat.add(x, Nat.add(Nat.add(v, r), l)) == Nat.add(v, Nat.add(x, Nat.add(l, r))) : Nat}

def shuffle(x, v, r, l):
  Equal.trans(Nat, Nat.add(x, Nat.add(Nat.add(v, r), l)), Nat.add(x, Nat.add(v, Nat.add(r, l))),
    Nat.add(v, Nat.add(x, Nat.add(l, r))),
    add_r(x, Nat.add(Nat.add(v, r), l), Nat.add(v, Nat.add(r, l)), add_assoc(v, r, l)),
    Equal.trans(Nat, Nat.add(x, Nat.add(v, Nat.add(r, l))), Nat.add(v, Nat.add(x, Nat.add(r, l))),
      Nat.add(v, Nat.add(x, Nat.add(l, r))),
      add_swap(x, v, Nat.add(r, l)),
      add_r(v, Nat.add(x, Nat.add(r, l)), Nat.add(x, Nat.add(l, r)),
        add_r(x, Nat.add(r, l), Nat.add(l, r), add_comm(r, l)))))

# From o == 0 and 1 <= o + c, 1 <= c.
law pos_tail:
  for -o: Nat
  for -c: Nat
  for e: {o == 0n : Nat}
  for p: {Nat.is_le(1n, Nat.add(o, c)) == True{} : Bool}
  {Nat.is_le(1n, c) == True{} : Bool}

def pos_tail(o, c, e, p):
  Equal.trans(Bool, Nat.is_le(1n, c), Nat.is_le(1n, Nat.add(o, c)), True{},
    Equal.cong(Nat, Bool, n => Nat.is_le(1n, Nat.add(n, c)), 0n, o, Equal.sym(Nat, o, 0n, e)),
    p)

# is_eq(a, b) with a rewritten.
law is_eq_l:
  for -a: Nat
  for -b: Nat
  for -c: Nat
  for ab: {a == b : Nat}
  for e: {Nat.is_eq(b, c) == True{} : Bool}
  {Nat.is_eq(a, c) == True{} : Bool}

def is_eq_l(a, b, c, ab, e):
  %Equal.sym(Nat, a, b, ab) : {Nat.is_eq(_, c) == True{} : Bool}
  e

law is_eq_of:
  for +a: Nat
  for -b: Nat
  for e: {a == b : Nat}
  {Nat.is_eq(a, b) == True{} : Bool}

def is_eq_of(a, b, e):
  %e : {Nat.is_eq(a, _) == True{} : Bool}
  eq_refl(a)

law pos_one:
  for -o: Nat
  for +c: Nat
  for e: {o == 1n : Nat}
  {Nat.is_le(1n, Nat.add(o, c)) == True{} : Bool}

def pos_one(o, c, e):
  %Equal.sym(Nat, o, 1n, e) : {Nat.is_le(1n, Nat.add(_, c)) == True{} : Bool}
  le_zero(c)

law le_one:
  for -o: Nat
  for +c: Nat
  for eo: {o == 1n : Nat}
  for ec: {Nat.is_le(1n, c) == False{} : Bool}
  {Nat.is_le(Nat.add(o, c), 1n) == True{} : Bool}

def le_one(o, c, eo, ec):
  match c:
    case 0n:
      %Equal.sym(Nat, o, 1n, eo) : {Nat.is_le(Nat.add(_, 0n), 1n) == True{} : Bool}
      {==}
    case 1n+p:
      clash(Nat.is_le(0n, p), {Nat.is_le(Nat.add(o, 1n+p), 1n) == True{} : Bool}, le_zero(p), ec)

law le_zero_add:
  for -o: Nat
  for -c: Nat
  for eo: {o == 0n : Nat}
  for ih: {Nat.is_le(c, 1n) == True{} : Bool}
  {Nat.is_le(Nat.add(o, c), 1n) == True{} : Bool}

def le_zero_add(o, c, eo, ih):
  %Equal.sym(Nat, o, 0n, eo) : {Nat.is_le(Nat.add(_, c), 1n) == True{} : Bool}
  ih

law sub_self:
  for +a: Nat
  {Nat.sub(a, a) == 0n : Nat}

def sub_self(a):
  match a:
    case 0n:
      {==}
    case 1n+p:
      sub_self(p)

law bool_refl:
  for +b: Bool
  {T.Bool.is_eq(b, b) == True{} : Bool}

def bool_refl(b):
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

law bool_of:
  for +a: Bool
  for +b: Bool
  for +e: {T.Bool.is_eq(a, b) == True{} : Bool}
  {a == b : Bool}

def bool_of(a, b, e):
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      never({True{} == False{} : Bool}, e)
    case False{} True{}:
      never({False{} == True{} : Bool}, e)
    case False{} False{}:
      {==}

law nats_refl:
  for +xs: List<&2, Nat>
  {T.Nats.is_eq(xs, xs) == True{} : Bool}

def nats_refl(xs):
  match xs:
    case Nil{}:
      {==}
    case +h <> t:
      and_i(Nat.is_eq(h, h), T.Nats.is_eq(t, t), eq_refl(h), nats_refl(t))

law nats_of:
  for +xs: List<&2, Nat>
  for +ys: List<&2, Nat>
  for +e: {T.Nats.is_eq(xs, ys) == True{} : Bool}
  {xs == ys : List<&2, Nat>}

def nats_of(xs, ys, e):
  match xs ys:
    case Nil{} Nil{}:
      {==}
    case Nil{} y <> yt:
      never({Nil{} == y <> yt : List<&2, Nat>}, e)
    case x <> xt Nil{}:
      never({x <> xt == Nil{} : List<&2, Nat>}, e)
    case x <> xt y <> yt:
      %eq_of(x, y, and_l(Nat.is_eq(x, y), T.Nats.is_eq(xt, yt), e)) : {x <> xt == _ <> yt : List<&2, Nat>}
      %nats_of(xt, yt, and_r(Nat.is_eq(x, y), T.Nats.is_eq(xt, yt), e)) : {x <> xt == x <> _ : List<&2, Nat>}
      {==}

# (a + b) + (c + d) == (a + c) + (b + d)
law add_four:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for +d: Nat
  {Nat.add(Nat.add(a, b), Nat.add(c, d)) == Nat.add(Nat.add(a, c), Nat.add(b, d)) : Nat}

def add_four(a, b, c, d):
  Equal.trans(Nat, Nat.add(Nat.add(a, b), Nat.add(c, d)), Nat.add(a, Nat.add(b, Nat.add(c, d))),
    Nat.add(Nat.add(a, c), Nat.add(b, d)),
    add_assoc(a, b, Nat.add(c, d)),
    Equal.trans(Nat, Nat.add(a, Nat.add(b, Nat.add(c, d))), Nat.add(a, Nat.add(c, Nat.add(b, d))),
      Nat.add(Nat.add(a, c), Nat.add(b, d)),
      add_r(a, Nat.add(b, Nat.add(c, d)), Nat.add(c, Nat.add(b, d)), add_swap(b, c, d)),
      Equal.sym(Nat, Nat.add(Nat.add(a, c), Nat.add(b, d)), Nat.add(a, Nat.add(c, Nat.add(b, d))),
        add_assoc(a, c, Nat.add(b, d)))))

# r + ((s + b) + e) == (r + s) + (b + e)
law shed_assoc:
  for +r: Nat
  for +s: Nat
  for +b: Nat
  for +e: Nat
  {Nat.add(r, Nat.add(Nat.add(s, b), e)) == Nat.add(Nat.add(r, s), Nat.add(b, e)) : Nat}

def shed_assoc(r, s, b, e):
  Equal.trans(Nat, Nat.add(r, Nat.add(Nat.add(s, b), e)), Nat.add(r, Nat.add(s, Nat.add(b, e))),
    Nat.add(Nat.add(r, s), Nat.add(b, e)),
    add_r(r, Nat.add(Nat.add(s, b), e), Nat.add(s, Nat.add(b, e)), add_assoc(s, b, e)),
    Equal.sym(Nat, Nat.add(Nat.add(r, s), Nat.add(b, e)), Nat.add(r, Nat.add(s, Nat.add(b, e))),
      add_assoc(r, s, Nat.add(b, e))))

# Two things that add to zero are both zero.
law add_zero_l:
  for +a: Nat
  for -b: Nat
  for e: {Nat.add(a, b) == 0n : Nat}
  {a == 0n : Nat}

def Zero(n: Nat) -> Type:
  match n:
    case 0n:
      Empty
    case 1n+p:
      Unit

def add_zero_l(a, b, e):
  match a:
    case 0n:
      {==}
    case 1n+p:
      Empty.absurd({1n+p == 0n : Nat}, %e : Zero(_)
        Unit{})

law or_l:
  for +a: Bool
  for -b: Bool
  for e: {Bool.or(a, b) == False{} : Bool}
  {a == False{} : Bool}

def or_l(a, b, e):
  match a:
    case True{}:
      Equal.sym(Bool, False{}, True{}, Equal.sym(Bool, True{}, False{}, e))
    case False{}:
      {==}

law or_r:
  for +a: Bool
  for -b: Bool
  for e: {Bool.or(a, b) == False{} : Bool}
  {b == False{} : Bool}

def or_r(a, b, e):
  match a:
    case True{}:
      clash(True{}, {b == False{} : Bool}, {==}, e)
    case False{}:
      e

law add_both_zero:
  for -a: Nat
  for -b: Nat
  for ea: {a == 0n : Nat}
  for eb: {b == 0n : Nat}
  {Nat.add(a, b) == 0n : Nat}

def add_both_zero(a, b, ea, eb):
  %Equal.sym(Nat, a, 0n, ea) : {Nat.add(_, b) == 0n : Nat}
  eb

# From a <= b and a != b, a < b.
law lt_of_le_ne:
  for +a: Nat
  for +b: Nat
  for +le: {Nat.is_le(a, b) == True{} : Bool}
  for +ne: {Nat.is_eq(b, a) == False{} : Bool}
  {Nat.is_le(1n+a, b) == True{} : Bool}

def lt_of_le_ne(a, b, le, ne):
  match a b:
    case 0n 0n:
      never({Nat.is_le(1n, 0n) == True{} : Bool}, Equal.sym(Bool, True{}, False{}, ne))
    case 0n 1n+q:
      le_zero(q)
    case 1n+p 0n:
      never({Nat.is_le(2n+p, 0n) == True{} : Bool}, le)
    case 1n+p 1n+q:
      lt_of_le_ne(p, q, le, ne)

law add_both:
  for -a: Nat
  for -b: Nat
  for -c: Nat
  for -d: Nat
  for ab: {a == b : Nat}
  for cd: {c == d : Nat}
  {Nat.add(a, c) == Nat.add(b, d) : Nat}

def add_both(a, b, c, d, ab, cd):
  Equal.trans(Nat, Nat.add(a, c), Nat.add(b, c), Nat.add(b, d), add_l(a, b, c, ab), add_r(b, c, d, cd))

# (o + r) + (c + e) == r + ((o + c) + e)
law fill_assoc:
  for +o: Nat
  for +r: Nat
  for +c: Nat
  for +e: Nat
  {Nat.add(Nat.add(o, r), Nat.add(c, e)) == Nat.add(r, Nat.add(Nat.add(o, c), e)) : Nat}

def fill_assoc(o, r, c, e):
  Equal.trans(Nat, Nat.add(Nat.add(o, r), Nat.add(c, e)), Nat.add(Nat.add(r, o), Nat.add(c, e)),
    Nat.add(r, Nat.add(Nat.add(o, c), e)),
    add_l(Nat.add(o, r), Nat.add(r, o), Nat.add(c, e), add_comm(o, r)),
    Equal.sym(Nat, Nat.add(r, Nat.add(Nat.add(o, c), e)), Nat.add(Nat.add(r, o), Nat.add(c, e)), shed_assoc(r, o, c, e)))

# (o + j) + (r + t), rearranged to o + (j + (r + t))
law take_o:
  for +o: Nat
  for +j: Nat
  for -x: Nat
  {Nat.add(Nat.add(o, j), x) == Nat.add(o, Nat.add(j, x)) : Nat}

def take_o(o, j, x):
  add_assoc(o, j, x)

# n is exactly 1 when it's above 0 and at most 1.
law one_of:
  for +n: Nat
  for +p: {Nat.is_gt(n, 0n) == True{} : Bool}
  for +q: {Nat.is_le(n, 1n) == True{} : Bool}
  {n == 1n : Nat}

def one_of(n, p, q):
  match n:
    case 0n:
      never({0n == 1n : Nat}, p)
    case 1n+0n:
      {==}
    case 2n+m:
      never({2n+m == 1n : Nat}, q)

law zero_of:
  for +n: Nat
  for +p: {Nat.is_gt(n, 0n) == False{} : Bool}
  {n == 0n : Nat}

def zero_of(n, p):
  match n:
    case 0n:
      {==}
    case 1n+m:
      never({1n+m == 0n : Nat}, Equal.sym(Bool, True{}, False{}, p))

law le_add_r:
  for +a: Nat
  for +b: Nat
  {Nat.is_le(b, Nat.add(a, b)) == True{} : Bool}

law le_succ_r:
  for +a: Nat
  for +b: Nat
  for +e: {Nat.is_le(a, b) == True{} : Bool}
  {Nat.is_le(a, 1n+b) == True{} : Bool}

def le_succ_r(a, b, e):
  le_trans(a, b, 1n+b, e, le_step(b))

def le_add_r(a, b):
  match a:
    case 0n:
      le_refl(b)
    case 1n+p:
      le_succ_r(b, Nat.add(p, b), le_add_r(p, b))

law le_add_l:
  for +a: Nat
  for +b: Nat
  {Nat.is_le(a, Nat.add(a, b)) == True{} : Bool}

def le_add_l(a, b):
  match a:
    case 0n:
      le_zero(b)
    case 1n+p:
      le_add_l(p, b)

law or_true:
  for +a: Bool
  {Bool.or(a, True{}) == True{} : Bool}

def or_true(a):
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

law not_of:
  for +b: Bool
  for e: {b == False{} : Bool}
  {Bool.not(b) == True{} : Bool}

def not_of(b, e):
  %Equal.sym(Bool, b, False{}, e) : {Bool.not(_) == True{} : Bool}
  {==}

law or_left:
  for +a: Bool
  for -b: Bool
  for e: {a == True{} : Bool}
  {Bool.or(a, b) == True{} : Bool}

def or_left(a, b, e):
  match a:
    case True{}:
      {==}
    case False{}:
      never({b == True{} : Bool}, e)

law or_right:
  for +a: Bool
  for -b: Bool
  for e: {b == True{} : Bool}
  {Bool.or(a, b) == True{} : Bool}

def or_right(a, b, e):
  match a:
    case True{}:
      {==}
    case False{}:
      e

law or_rest:
  for +a: Bool
  for -b: Bool
  for e: {Bool.or(a, b) == True{} : Bool}
  for f: {a == False{} : Bool}
  {b == True{} : Bool}

def or_rest(a, b, e, f):
  match a:
    case True{}:
      never({b == True{} : Bool}, Equal.sym(Bool, True{}, False{}, f))
    case False{}:
      e

law and_false:
  for +a: Bool
  {Bool.and(a, False{}) == False{} : Bool}

def and_false(a):
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

law lt_self:
  for +a: Nat
  {Nat.is_lt(a, a) == False{} : Bool}

def lt_self(a):
  match a:
    case 0n:
      {==}
    case 1n+p:
      lt_self(p)

law lt_trans:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for +ab: {Nat.is_lt(a, b) == True{} : Bool}
  for +bc: {Nat.is_lt(b, c) == True{} : Bool}
  {Nat.is_lt(a, c) == True{} : Bool}

def lt_trans(a, b, c, ab, bc):
  match a b c:
    case 0n 0n _:
      never({Nat.is_lt(0n, c) == True{} : Bool}, ab)
    case 0n 1n+q 0n:
      never({False{} == True{} : Bool}, bc)
    case 0n 1n+q 1n+r:
      {==}
    case 1n+p 0n _:
      never({Nat.is_lt(1n+p, c) == True{} : Bool}, ab)
    case 1n+p 1n+q 0n:
      never({False{} == True{} : Bool}, bc)
    case 1n+p 1n+q 1n+r:
      lt_trans(p, q, r, ab, bc)

law and_assoc:
  for +a: Bool
  for -b: Bool
  for -c: Bool
  {Bool.and(a, Bool.and(b, c)) == Bool.and(Bool.and(a, b), c) : Bool}

def and_assoc(a, b, c):
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

law lt_zero:
  for +a: Nat
  {Nat.is_lt(a, 0n) == False{} : Bool}

def lt_zero(a):
  match a:
    case 0n:
      {==}
    case 1n+p:
      {==}

law le_of_lt:
  for +a: Nat
  for +b: Nat
  for +e: {Nat.is_lt(a, b) == True{} : Bool}
  {Nat.is_le(a, b) == True{} : Bool}

def le_of_lt(a, b, e):
  match a b:
    case 0n _:
      le_zero(b)
    case 1n+p 0n:
      never({False{} == True{} : Bool}, e)
    case 1n+p 1n+q:
      le_of_lt(p, q, e)

# z < x and not y < x give z < y.
law lt_not_lt:
  for +z: Nat
  for +x: Nat
  for +y: Nat
  for +zx: {Nat.is_lt(z, x) == True{} : Bool}
  for +yx: {Nat.is_lt(y, x) == False{} : Bool}
  {Nat.is_lt(z, y) == True{} : Bool}

def lt_not_lt(z, x, y, zx, yx):
  match z x y:
    case _ 0n 0n:
      clash(Nat.is_lt(z, 0n), {Nat.is_lt(z, 0n) == True{} : Bool}, zx, lt_zero(z))
    case _ 0n 1n+q:
      clash(Nat.is_lt(z, 0n), {Nat.is_lt(z, 1n+q) == True{} : Bool}, zx, lt_zero(z))
    case 0n 1n+p 0n:
      never({Nat.is_lt(0n, 0n) == True{} : Bool}, Equal.sym(Bool, True{}, False{}, yx))
    case 0n 1n+p 1n+q:
      {==}
    case 1n+a 1n+p 0n:
      never({Nat.is_lt(1n+a, 0n) == True{} : Bool}, Equal.sym(Bool, True{}, False{}, yx))
    case 1n+a 1n+p 1n+q:
      lt_not_lt(a, p, q, zx, yx)

law not_t:
  for +b: Bool
  for e: {Bool.not(b) == True{} : Bool}
  {b == False{} : Bool}

def not_t(b, e):
  match b:
    case True{}:
      never({True{} == False{} : Bool}, Equal.sym(Bool, True{}, False{}, Equal.sym(Bool, False{}, True{}, e)))
    case False{}:
      {==}
