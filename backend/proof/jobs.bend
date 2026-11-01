import Base
import ../core/types.bend as T
import ../core/jobs.bend as J
import ./logic.bend as L

# Lists of appraisals as bags: reflection for Appraisal.is_eq, then the sort is
# a permutation, and sorted lists with the same counts are the same list.

# A universally quantified hypothesis is an affine closure, so it can't be used
# twice. agree states the same thing over a concrete list, and is reusable.
def agree(zs: List<&2, T.Appraisal>, +xs: List<&2, T.Appraisal>, +ys: List<&2, T.Appraisal>) -> Bool:
  match zs:
    case Nil{}:
      True{}
    case +z <> t:
      Bool.and(Nat.is_eq(J.count(z, xs), J.count(z, ys)), agree(t, xs, ys))

# Sorted, allowing repeats. Only proofs need this.
def asc(xs: List<&2, T.Appraisal>, lo: Nat) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case +h <> t:
      Bool.and(Nat.is_le(lo, T.Appraisal.id(h)), asc(t, T.Appraisal.id(h)))

# Point and Appraisal equality
# ----------------------------

law point_refl:
  for +p: T.Point
  {T.Point.is_eq(p, p) == True{} : Bool}

def point_refl(p):
  match p:
    case T.Point{a, b}:
      L.and_i(Nat.is_eq(a, a), Nat.is_eq(b, b), L.eq_refl(a), L.eq_refl(b))

law point_of:
  for +p: T.Point
  for +q: T.Point
  for +e: {T.Point.is_eq(p, q) == True{} : Bool}
  {p == q : T.Point}

def point_of(p, q, e):
  match p q:
    case T.Point{a, b} T.Point{c, d}:
      %L.eq_of(a, c, L.and_l(Nat.is_eq(a, c), Nat.is_eq(b, d), e)) : {T.Point{a, b} == T.Point{_, d} : T.Point}
      %L.eq_of(b, d, L.and_r(Nat.is_eq(a, c), Nat.is_eq(b, d), e)) : {T.Point{a, b} == T.Point{a, _} : T.Point}
      {==}

law app_refl:
  for +a: T.Appraisal
  {T.Appraisal.is_eq(a, a) == True{} : Bool}

def app_refl(a):
  match a:
    case T.Appraisal{i, s, z, d, m, t}:
      +r4 = Bool.and(Nat.is_eq(m, m), Nat.is_eq(t, t))
      +r3 = Bool.and(Nat.is_eq(d, d), r4)
      +r2 = Bool.and(Nat.is_eq(z, z), r3)
      +r1 = Bool.and(T.Point.is_eq(s, s), r2)
      L.and_i(Nat.is_eq(i, i), r1, L.eq_refl(i),
      L.and_i(T.Point.is_eq(s, s), r2, point_refl(s),
      L.and_i(Nat.is_eq(z, z), r3, L.eq_refl(z),
      L.and_i(Nat.is_eq(d, d), r4, L.eq_refl(d),
      L.and_i(Nat.is_eq(m, m), Nat.is_eq(t, t), L.eq_refl(m), L.eq_refl(t))))))

law app_of.go:
  for +i1: Nat
  for +i2: Nat
  for +s1: T.Point
  for +s2: T.Point
  for +z1: Nat
  for +z2: Nat
  for +d1: Nat
  for +d2: Nat
  for +m1: Nat
  for +m2: Nat
  for +t1: Nat
  for +t2: Nat
  for +ei: {i1 == i2 : Nat}
  for +es: {s1 == s2 : T.Point}
  for +ez: {z1 == z2 : Nat}
  for +ed: {d1 == d2 : Nat}
  for +em: {m1 == m2 : Nat}
  for +et: {t1 == t2 : Nat}
  {T.Appraisal{i1, s1, z1, d1, m1, t1} == T.Appraisal{i2, s2, z2, d2, m2, t2} : T.Appraisal}

def app_of.go(i1, i2, s1, s2, z1, z2, d1, d2, m1, m2, t1, t2, ei, es, ez, ed, em, et):
  %ei : {T.Appraisal{i1, s1, z1, d1, m1, t1} == T.Appraisal{_, s2, z2, d2, m2, t2} : T.Appraisal}
  %es : {T.Appraisal{i1, s1, z1, d1, m1, t1} == T.Appraisal{i1, _, z2, d2, m2, t2} : T.Appraisal}
  %ez : {T.Appraisal{i1, s1, z1, d1, m1, t1} == T.Appraisal{i1, s1, _, d2, m2, t2} : T.Appraisal}
  %ed : {T.Appraisal{i1, s1, z1, d1, m1, t1} == T.Appraisal{i1, s1, z1, _, m2, t2} : T.Appraisal}
  %em : {T.Appraisal{i1, s1, z1, d1, m1, t1} == T.Appraisal{i1, s1, z1, d1, _, t2} : T.Appraisal}
  %et : {T.Appraisal{i1, s1, z1, d1, m1, t1} == T.Appraisal{i1, s1, z1, d1, m1, _} : T.Appraisal}
  {==}

law app_of:
  for +a: T.Appraisal
  for +b: T.Appraisal
  for +e: {T.Appraisal.is_eq(a, b) == True{} : Bool}
  {a == b : T.Appraisal}

def app_of(a, b, e):
  match a b:
    case T.Appraisal{i1, s1, z1, d1, m1, t1} T.Appraisal{i2, s2, z2, d2, m2, t2}:
      +r4 = Bool.and(Nat.is_eq(m1, m2), Nat.is_eq(t1, t2))
      +r3 = Bool.and(Nat.is_eq(d1, d2), r4)
      +r2 = Bool.and(Nat.is_eq(z1, z2), r3)
      +r1 = Bool.and(T.Point.is_eq(s1, s2), r2)
      +e1 = L.and_r(Nat.is_eq(i1, i2), r1, e)
      +e2 = L.and_r(T.Point.is_eq(s1, s2), r2, e1)
      +e3 = L.and_r(Nat.is_eq(z1, z2), r3, e2)
      +e4 = L.and_r(Nat.is_eq(d1, d2), r4, e3)
      app_of.go(i1, i2, s1, s2, z1, z2, d1, d2, m1, m2, t1, t2,
        L.eq_of(i1, i2, L.and_l(Nat.is_eq(i1, i2), r1, e)),
        point_of(s1, s2, L.and_l(T.Point.is_eq(s1, s2), r2, e1)),
        L.eq_of(z1, z2, L.and_l(Nat.is_eq(z1, z2), r3, e2)),
        L.eq_of(d1, d2, L.and_l(Nat.is_eq(d1, d2), r4, e3)),
        L.eq_of(m1, m2, L.and_l(Nat.is_eq(m1, m2), Nat.is_eq(t1, t2), e4)),
        L.eq_of(t1, t2, L.and_r(Nat.is_eq(m1, m2), Nat.is_eq(t1, t2), e4)))

# Counting
# --------

law one_t:
  for +a: T.Appraisal
  for +b: T.Appraisal
  for +e: {T.Appraisal.is_eq(a, b) == True{} : Bool}
  {J.count.one(a, b) == 1n : Nat}

def one_t(a, b, e):
  %Equal.sym(Bool, T.Appraisal.is_eq(a, b), True{}, e) : {Bool.pick(Nat, _, 1n, 0n) == 1n : Nat}
  {==}

law one_f:
  for +a: T.Appraisal
  for +b: T.Appraisal
  for +e: {T.Appraisal.is_eq(a, b) == False{} : Bool}
  {J.count.one(a, b) == 0n : Nat}

def one_f(a, b, e):
  %Equal.sym(Bool, T.Appraisal.is_eq(a, b), False{}, e) : {Bool.pick(Nat, _, 1n, 0n) == 0n : Nat}
  {==}

law one_self:
  for +a: T.Appraisal
  {J.count.one(a, a) == 1n : Nat}

def one_self(a):
  one_t(a, a, app_refl(a))

law count_append:
  for +a: T.Appraisal
  for xs: List<&2, T.Appraisal>
  for +ys: List<&2, T.Appraisal>
  {J.count(a, List.append(&2, T.Appraisal, xs, ys)) == Nat.add(J.count(a, xs), J.count(a, ys)) : Nat}

def count_append(a, xs, ys):
  match xs:
    case Nil{}:
      {==}
    case +h <> t:
      L.assoc_step(J.count.one(a, h), J.count(a, List.append(&2, T.Appraisal, t, ys)),
        J.count(a, t), J.count(a, ys), count_append(a, t, ys))

# Merge
# -----

law merge_t:
  for +x: T.Appraisal
  for +xt: List<&2, T.Appraisal>
  for +y: T.Appraisal
  for +yt: List<&2, T.Appraisal>
  for +e: {J.le(x, y) == True{} : Bool}
  {J.merge(x <> xt, y <> yt) == x <> J.merge(xt, y <> yt) : List<&2, T.Appraisal>}

def merge_t(x, xt, y, yt, e):
  %Equal.sym(Bool, J.le(x, y), True{}, e) : {J.lazy(_, u => x <> J.merge(xt, y <> yt), u => y <> J.merge(x <> xt, yt)) == x <> J.merge(xt, y <> yt) : List<&2, T.Appraisal>}
  {==}

law merge_f:
  for +x: T.Appraisal
  for +xt: List<&2, T.Appraisal>
  for +y: T.Appraisal
  for +yt: List<&2, T.Appraisal>
  for +e: {J.le(x, y) == False{} : Bool}
  {J.merge(x <> xt, y <> yt) == y <> J.merge(x <> xt, yt) : List<&2, T.Appraisal>}

def merge_f(x, xt, y, yt, e):
  %Equal.sym(Bool, J.le(x, y), False{}, e) : {J.lazy(_, u => x <> J.merge(xt, y <> yt), u => y <> J.merge(x <> xt, yt)) == y <> J.merge(x <> xt, yt) : List<&2, T.Appraisal>}
  {==}

law count_merge.t:
  for +a: T.Appraisal
  for +x: T.Appraisal
  for +xt: List<&2, T.Appraisal>
  for +y: T.Appraisal
  for +yt: List<&2, T.Appraisal>
  for +e: {J.le(x, y) == True{} : Bool}
  for +ih: {J.count(a, J.merge(xt, y <> yt)) == Nat.add(J.count(a, xt), J.count(a, y <> yt)) : Nat}
  {J.count(a, J.merge(x <> xt, y <> yt)) == Nat.add(J.count(a, x <> xt), J.count(a, y <> yt)) : Nat}

def count_merge.t(a, x, xt, y, yt, e, ih):
  %Equal.sym(List<&2, T.Appraisal>, J.merge(x <> xt, y <> yt), x <> J.merge(xt, y <> yt), merge_t(x, xt, y, yt, e)) : {J.count(a, _) == Nat.add(J.count(a, x <> xt), J.count(a, y <> yt)) : Nat}
  L.assoc_step(J.count.one(a, x), J.count(a, J.merge(xt, y <> yt)), J.count(a, xt), J.count(a, y <> yt), ih)

law count_merge.f:
  for +a: T.Appraisal
  for +x: T.Appraisal
  for +xt: List<&2, T.Appraisal>
  for +y: T.Appraisal
  for +yt: List<&2, T.Appraisal>
  for +e: {J.le(x, y) == False{} : Bool}
  for +ih: {J.count(a, J.merge(x <> xt, yt)) == Nat.add(J.count(a, x <> xt), J.count(a, yt)) : Nat}
  {J.count(a, J.merge(x <> xt, y <> yt)) == Nat.add(J.count(a, x <> xt), J.count(a, y <> yt)) : Nat}

def count_merge.f(a, x, xt, y, yt, e, ih):
  %Equal.sym(List<&2, T.Appraisal>, J.merge(x <> xt, y <> yt), y <> J.merge(x <> xt, yt), merge_f(x, xt, y, yt, e)) : {J.count(a, _) == Nat.add(J.count(a, x <> xt), J.count(a, y <> yt)) : Nat}
  L.swap_step(J.count.one(a, y), J.count(a, J.merge(x <> xt, yt)), J.count(a, x <> xt), J.count(a, yt), ih)

law count_merge:
  for +a: T.Appraisal
  for +xs: List<&2, T.Appraisal>
  for +ys: List<&2, T.Appraisal>
  {J.count(a, J.merge(xs, ys)) == Nat.add(J.count(a, xs), J.count(a, ys)) : Nat}

def count_merge(a, xs, ys):
  match xs ys:
    case Nil{} _:
      {==}
    case x <> xt Nil{}:
      Equal.sym(Nat, Nat.add(J.count(a, x <> xt), 0n), J.count(a, x <> xt), L.add_zero(J.count(a, x <> xt)))
    case x <> xt y <> yt:
      L.cases(J.le(x, y), {J.count(a, J.merge(x <> xt, y <> yt)) == Nat.add(J.count(a, x <> xt), J.count(a, y <> yt)) : Nat},
        +e => count_merge.t(a, x, xt, y, yt, e, count_merge(a, xt, y <> yt)),
        +e => count_merge.f(a, x, xt, y, yt, e, count_merge(a, x <> xt, yt)))

# The sort is a permutation
# -------------------------

def C(+a: T.Appraisal, t: J.Tree) -> Nat:
  J.count(a, J.Tree.sort(t))

law count_bin:
  for +a: T.Appraisal
  for +x: T.Appraisal
  for +l: J.Tree
  for +r: J.Tree
  {C(a, J.Bin{x, l, r}) == Nat.add(J.count.one(a, x), Nat.add(C(a, l), C(a, r))) : Nat}

def count_bin(a, x, l, r):
  +sl = J.Tree.sort(l)
  +sr = J.Tree.sort(r)
  +m = J.merge(sl, sr)
  +o = J.count.one(a, x)
  Equal.trans(Nat, J.count(a, J.merge([x], m)), Nat.add(Nat.add(o, 0n), J.count(a, m)),
    Nat.add(o, Nat.add(J.count(a, sl), J.count(a, sr))),
    count_merge(a, [x], m),
    Equal.trans(Nat, Nat.add(Nat.add(o, 0n), J.count(a, m)), Nat.add(o, J.count(a, m)),
      Nat.add(o, Nat.add(J.count(a, sl), J.count(a, sr))),
      L.add_l(Nat.add(o, 0n), o, J.count(a, m), L.add_zero(o)),
      L.add_r(o, J.count(a, m), Nat.add(J.count(a, sl), J.count(a, sr)), count_merge(a, sl, sr))))

law count_add:
  for +a: T.Appraisal
  for +t: J.Tree
  for +v: T.Appraisal
  {C(a, J.Tree.add(t, v)) == Nat.add(J.count.one(a, v), C(a, t)) : Nat}

def count_add(a, t, v):
  match t:
    case J.Tip{}:
      {==}
    case J.Bin{x, l, r}:
      +ox = J.count.one(a, x)
      +ov = J.count.one(a, v)
      Equal.trans(Nat, C(a, J.Bin{x, J.Tree.add(r, v), l}), Nat.add(ox, Nat.add(C(a, J.Tree.add(r, v)), C(a, l))),
        Nat.add(ov, C(a, J.Bin{x, l, r})),
        count_bin(a, x, J.Tree.add(r, v), l),
        Equal.trans(Nat, Nat.add(ox, Nat.add(C(a, J.Tree.add(r, v)), C(a, l))),
          Nat.add(ox, Nat.add(Nat.add(ov, C(a, r)), C(a, l))), Nat.add(ov, C(a, J.Bin{x, l, r})),
          L.add_r(ox, Nat.add(C(a, J.Tree.add(r, v)), C(a, l)), Nat.add(Nat.add(ov, C(a, r)), C(a, l)),
            L.add_l(C(a, J.Tree.add(r, v)), Nat.add(ov, C(a, r)), C(a, l), count_add(a, r, v))),
          Equal.trans(Nat, Nat.add(ox, Nat.add(Nat.add(ov, C(a, r)), C(a, l))),
            Nat.add(ov, Nat.add(ox, Nat.add(C(a, l), C(a, r)))), Nat.add(ov, C(a, J.Bin{x, l, r})),
            L.shuffle(ox, ov, C(a, r), C(a, l)),
            L.add_r(ov, Nat.add(ox, Nat.add(C(a, l), C(a, r))), C(a, J.Bin{x, l, r}),
              Equal.sym(Nat, C(a, J.Bin{x, l, r}), Nat.add(ox, Nat.add(C(a, l), C(a, r))), count_bin(a, x, l, r)))))) 

law count_of:
  for +a: T.Appraisal
  for +xs: List<&2, T.Appraisal>
  for +t: J.Tree
  {C(a, J.Tree.of(xs, t)) == Nat.add(J.count(a, xs), C(a, t)) : Nat}

def count_of(a, xs, t):
  match xs:
    case Nil{}:
      {==}
    case +h <> r:
      +oh = J.count.one(a, h)
      +cr = J.count(a, r)
      Equal.trans(Nat, C(a, J.Tree.of(r, J.Tree.add(t, h))), Nat.add(cr, C(a, J.Tree.add(t, h))),
        Nat.add(Nat.add(oh, cr), C(a, t)),
        count_of(a, r, J.Tree.add(t, h)),
        Equal.trans(Nat, Nat.add(cr, C(a, J.Tree.add(t, h))), Nat.add(cr, Nat.add(oh, C(a, t))),
          Nat.add(Nat.add(oh, cr), C(a, t)),
          L.add_r(cr, C(a, J.Tree.add(t, h)), Nat.add(oh, C(a, t)), count_add(a, t, h)),
          Equal.trans(Nat, Nat.add(cr, Nat.add(oh, C(a, t))), Nat.add(oh, Nat.add(cr, C(a, t))),
            Nat.add(Nat.add(oh, cr), C(a, t)),
            L.add_swap(cr, oh, C(a, t)),
            Equal.sym(Nat, Nat.add(Nat.add(oh, cr), C(a, t)), Nat.add(oh, Nat.add(cr, C(a, t))),
              L.add_assoc(oh, cr, C(a, t))))))

law count_sort:
  for +a: T.Appraisal
  for +xs: List<&2, T.Appraisal>
  {J.count(a, J.sort(xs)) == J.count(a, xs) : Nat}

def count_sort(a, xs):
  Equal.trans(Nat, C(a, J.Tree.of(xs, J.Tip{})), Nat.add(J.count(a, xs), 0n), J.count(a, xs),
    count_of(a, xs, J.Tip{}), L.add_zero(J.count(a, xs)))

# The sort sorts
# --------------

law asc_merge.t:
  for +lo: Nat
  for +x: T.Appraisal
  for +xt: List<&2, T.Appraisal>
  for +y: T.Appraisal
  for +yt: List<&2, T.Appraisal>
  for +e: {J.le(x, y) == True{} : Bool}
  for +lx: {Nat.is_le(lo, T.Appraisal.id(x)) == True{} : Bool}
  for +ih: {asc(J.merge(xt, y <> yt), T.Appraisal.id(x)) == True{} : Bool}
  {asc(J.merge(x <> xt, y <> yt), lo) == True{} : Bool}

def asc_merge.t(lo, x, xt, y, yt, e, lx, ih):
  %Equal.sym(List<&2, T.Appraisal>, J.merge(x <> xt, y <> yt), x <> J.merge(xt, y <> yt), merge_t(x, xt, y, yt, e)) : {asc(_, lo) == True{} : Bool}
  L.and_i(Nat.is_le(lo, T.Appraisal.id(x)), asc(J.merge(xt, y <> yt), T.Appraisal.id(x)), lx, ih)

law asc_merge.f:
  for +lo: Nat
  for +x: T.Appraisal
  for +xt: List<&2, T.Appraisal>
  for +y: T.Appraisal
  for +yt: List<&2, T.Appraisal>
  for +e: {J.le(x, y) == False{} : Bool}
  for +ly: {Nat.is_le(lo, T.Appraisal.id(y)) == True{} : Bool}
  for +ih: {asc(J.merge(x <> xt, yt), T.Appraisal.id(y)) == True{} : Bool}
  {asc(J.merge(x <> xt, y <> yt), lo) == True{} : Bool}

def asc_merge.f(lo, x, xt, y, yt, e, ly, ih):
  %Equal.sym(List<&2, T.Appraisal>, J.merge(x <> xt, y <> yt), y <> J.merge(x <> xt, yt), merge_f(x, xt, y, yt, e)) : {asc(_, lo) == True{} : Bool}
  L.and_i(Nat.is_le(lo, T.Appraisal.id(y)), asc(J.merge(x <> xt, yt), T.Appraisal.id(y)), ly, ih)

law asc_merge:
  for +xs: List<&2, T.Appraisal>
  for +ys: List<&2, T.Appraisal>
  for +lo: Nat
  for +ex: {asc(xs, lo) == True{} : Bool}
  for +ey: {asc(ys, lo) == True{} : Bool}
  {asc(J.merge(xs, ys), lo) == True{} : Bool}

def asc_merge(xs, ys, lo, ex, ey):
  match xs ys:
    case Nil{} _:
      ey
    case x <> xt Nil{}:
      ex
    case x <> xt y <> yt:
      +ix = T.Appraisal.id(x)
      +iy = T.Appraisal.id(y)
      L.cases(J.le(x, y), {asc(J.merge(x <> xt, y <> yt), lo) == True{} : Bool},
        +e => asc_merge.t(lo, x, xt, y, yt, e, L.and_l(Nat.is_le(lo, ix), asc(xt, ix), ex),
          asc_merge(xt, y <> yt, ix, L.and_r(Nat.is_le(lo, ix), asc(xt, ix), ex),
            L.and_i(Nat.is_le(ix, iy), asc(yt, iy), e, L.and_r(Nat.is_le(lo, iy), asc(yt, iy), ey)))),
        +e => asc_merge.f(lo, x, xt, y, yt, e, L.and_l(Nat.is_le(lo, iy), asc(yt, iy), ey),
          asc_merge(x <> xt, yt, iy,
            L.and_i(Nat.is_le(iy, ix), asc(xt, ix), L.le_weak(iy, ix, L.le_total(ix, iy, e)),
              L.and_r(Nat.is_le(lo, ix), asc(xt, ix), ex)),
            L.and_r(Nat.is_le(lo, iy), asc(yt, iy), ey))))

law asc_tree:
  for +t: J.Tree
  {asc(J.Tree.sort(t), 0n) == True{} : Bool}

def asc_tree(t):
  match t:
    case J.Tip{}:
      {==}
    case J.Bin{x, l, r}:
      asc_merge([x], J.merge(J.Tree.sort(l), J.Tree.sort(r)), 0n,
        L.and_i(Nat.is_le(0n, T.Appraisal.id(x)), True{}, L.le_zero(T.Appraisal.id(x)), {==}),
        asc_merge(J.Tree.sort(l), J.Tree.sort(r), 0n, asc_tree(l), asc_tree(r)))

law asc_sort:
  for +xs: List<&2, T.Appraisal>
  {asc(J.sort(xs), 0n) == True{} : Bool}

def asc_sort(xs):
  asc_tree(J.Tree.of(xs, J.Tip{}))

# Sorted lists with the same counts are the same list
# ---------------------------------------------------

law rising_low:
  for +a: T.Appraisal
  for +ys: List<&2, T.Appraisal>
  for +lo: Nat
  for +er: {J.rising(ys, lo) == True{} : Bool}
  for +ec: {Nat.is_le(1n, J.count(a, ys)) == True{} : Bool}
  {Nat.is_le(lo, T.Appraisal.id(a)) == True{} : Bool}

def rising_low(a, ys, lo, er, ec):
  match ys:
    case Nil{}:
      L.never({Nat.is_le(lo, T.Appraisal.id(a)) == True{} : Bool}, ec)
    case +h <> t:
      +ih = T.Appraisal.id(h)
      +ia = T.Appraisal.id(a)
      L.cases(T.Appraisal.is_eq(a, h), {Nat.is_le(lo, ia) == True{} : Bool},
        +e =>
          %Equal.sym(T.Appraisal, a, h, app_of(a, h, e)) : {Nat.is_le(lo, T.Appraisal.id(_)) == True{} : Bool}
          L.and_l(Nat.is_le(lo, ih), J.rising(t, 1n+ih), er),
        +e =>
          L.le_trans(lo, ih, ia, L.and_l(Nat.is_le(lo, ih), J.rising(t, 1n+ih), er),
            L.le_weak(ih, ia, rising_low(a, t, 1n+ih, L.and_r(Nat.is_le(lo, ih), J.rising(t, 1n+ih), er),
              L.pos_tail(J.count.one(a, h), J.count(a, t), one_f(a, h, e), ec)))))

law asc_low:
  for +a: T.Appraisal
  for +xs: List<&2, T.Appraisal>
  for +lo: Nat
  for +er: {asc(xs, lo) == True{} : Bool}
  for +ec: {Nat.is_le(1n, J.count(a, xs)) == True{} : Bool}
  {Nat.is_le(lo, T.Appraisal.id(a)) == True{} : Bool}

def asc_low(a, xs, lo, er, ec):
  match xs:
    case Nil{}:
      L.never({Nat.is_le(lo, T.Appraisal.id(a)) == True{} : Bool}, ec)
    case +h <> t:
      +ih = T.Appraisal.id(h)
      +ia = T.Appraisal.id(a)
      L.cases(T.Appraisal.is_eq(a, h), {Nat.is_le(lo, ia) == True{} : Bool},
        +e =>
          %Equal.sym(T.Appraisal, a, h, app_of(a, h, e)) : {Nat.is_le(lo, T.Appraisal.id(_)) == True{} : Bool}
          L.and_l(Nat.is_le(lo, ih), asc(t, ih), er),
        +e =>
          L.le_trans(lo, ih, ia, L.and_l(Nat.is_le(lo, ih), asc(t, ih), er),
            asc_low(a, t, ih, L.and_r(Nat.is_le(lo, ih), asc(t, ih), er),
              L.pos_tail(J.count.one(a, h), J.count(a, t), one_f(a, h, e), ec))))

# Dropping equal heads from both lists keeps the counts equal.
law agree_tail:
  for +zs: List<&2, T.Appraisal>
  for +x: T.Appraisal
  for +y: T.Appraisal
  for +xt: List<&2, T.Appraisal>
  for +yt: List<&2, T.Appraisal>
  for +exy: {x == y : T.Appraisal}
  for +e: {agree(zs, x <> xt, y <> yt) == True{} : Bool}
  {agree(zs, xt, yt) == True{} : Bool}

law cancel_at:
  for +z: T.Appraisal
  for +x: T.Appraisal
  for +y: T.Appraisal
  for +xt: List<&2, T.Appraisal>
  for +yt: List<&2, T.Appraisal>
  for +exy: {x == y : T.Appraisal}
  for +e: {Nat.is_eq(J.count(z, x <> xt), J.count(z, y <> yt)) == True{} : Bool}
  {Nat.is_eq(J.count(z, xt), J.count(z, yt)) == True{} : Bool}

def cancel_at(z, x, y, xt, yt, exy, e):
  +o = J.count.one(z, x)
  +cx = J.count(z, xt)
  +cy = J.count(z, yt)
  +step = L.eq_of(Nat.add(o, cx), J.count(z, y <> yt), e)
  +fix = {%Equal.sym(T.Appraisal, x, y, exy) : {Nat.add(J.count.one(z, y), cy) == Nat.add(J.count.one(z, _), cy) : Nat}
    {==} : {Nat.add(J.count.one(z, y), cy) == Nat.add(o, cy) : Nat}}
  L.is_eq_of(cx, cy, L.add_cancel(o, cx, cy,
    Equal.trans(Nat, Nat.add(o, cx), Nat.add(J.count.one(z, y), cy), Nat.add(o, cy), step, fix)))

def agree_tail(zs, x, y, xt, yt, exy, e):
  match zs:
    case Nil{}:
      {==}
    case +z <> t:
      +hd = Nat.is_eq(J.count(z, x <> xt), J.count(z, y <> yt))
      +tl = agree(t, x <> xt, y <> yt)
      L.and_i(Nat.is_eq(J.count(z, xt), J.count(z, yt)), agree(t, xt, yt),
        cancel_at(z, x, y, xt, yt, exy, L.and_l(hd, tl, e)),
        agree_tail(t, x, y, xt, yt, exy, L.and_r(hd, tl, e)))

law same_cons.t:
  for +x: T.Appraisal
  for +xt: List<&2, T.Appraisal>
  for +y: T.Appraisal
  for +yt: List<&2, T.Appraisal>
  for +e: {T.Appraisal.is_eq(x, y) == True{} : Bool}
  for +ih: {J.same(xt, yt) == True{} : Bool}
  {J.same(x <> xt, y <> yt) == True{} : Bool}

def same_cons.t(x, xt, y, yt, e, ih):
  L.and_i(T.Appraisal.is_eq(x, y), J.same(xt, yt), e, ih)

law agree_head:
  for +z: T.Appraisal
  for +t: List<&2, T.Appraisal>
  for +xs: List<&2, T.Appraisal>
  for +ys: List<&2, T.Appraisal>
  for +e: {agree(z <> t, xs, ys) == True{} : Bool}
  {J.count(z, xs) == J.count(z, ys) : Nat}

def agree_head(z, t, xs, ys, e):
  L.eq_of(J.count(z, xs), J.count(z, ys),
    L.and_l(Nat.is_eq(J.count(z, xs), J.count(z, ys)), agree(t, xs, ys), e))

law agree_rest:
  for +z: T.Appraisal
  for +t: List<&2, T.Appraisal>
  for +xs: List<&2, T.Appraisal>
  for +ys: List<&2, T.Appraisal>
  for +e: {agree(z <> t, xs, ys) == True{} : Bool}
  {agree(t, xs, ys) == True{} : Bool}

def agree_rest(z, t, xs, ys, e):
  L.and_r(Nat.is_eq(J.count(z, xs), J.count(z, ys)), agree(t, xs, ys), e)

law pos_self:
  for +x: T.Appraisal
  for +t: List<&2, T.Appraisal>
  {Nat.is_le(1n, J.count(x, x <> t)) == True{} : Bool}

def pos_self(x, t):
  L.pos_one(J.count.one(x, x), J.count(x, t), one_self(x))

# A positive count moved across an equality of counts.
law pos_move:
  for -a: Nat
  for -b: Nat
  for +e: {a == b : Nat}
  for +p: {Nat.is_le(1n, a) == True{} : Bool}
  {Nat.is_le(1n, b) == True{} : Bool}

def pos_move(a, b, e, p):
  %e : {Nat.is_le(1n, _) == True{} : Bool}
  p

# Heads that differ can't both be the smallest element of the same bag.
law heads_equal:
  for +x: T.Appraisal
  for +xt: List<&2, T.Appraisal>
  for +y: T.Appraisal
  for +yt: List<&2, T.Appraisal>
  for +lo: Nat
  for +hi: Nat
  for +ex: {asc(x <> xt, lo) == True{} : Bool}
  for +ey: {J.rising(y <> yt, hi) == True{} : Bool}
  for +cx: {J.count(x, x <> xt) == J.count(x, y <> yt) : Nat}
  for +cy: {J.count(y, x <> xt) == J.count(y, y <> yt) : Nat}
  {T.Appraisal.is_eq(x, y) == True{} : Bool}

def heads_equal(x, xt, y, yt, lo, hi, ex, ey, cx, cy):
  +ix = T.Appraisal.id(x)
  +iy = T.Appraisal.id(y)
  L.cases(T.Appraisal.is_eq(x, y), {T.Appraisal.is_eq(x, y) == True{} : Bool},
    +e => e,
    +e =>
      L.cases(T.Appraisal.is_eq(y, x), {T.Appraisal.is_eq(x, y) == True{} : Bool},
        +f =>
          %app_of(y, x, f) : {T.Appraisal.is_eq(_, y) == True{} : Bool}
          app_refl(y),
        +f =>
          +px = L.pos_tail(J.count.one(x, y), J.count(x, yt), one_f(x, y, e),
            pos_move(J.count(x, x <> xt), J.count(x, y <> yt), cx, pos_self(x, xt)))
          +py = L.pos_tail(J.count.one(y, x), J.count(y, xt), one_f(y, x, f),
            pos_move(J.count(y, y <> yt), J.count(y, x <> xt),
              Equal.sym(Nat, J.count(y, x <> xt), J.count(y, y <> yt), cy), pos_self(y, yt)))
          +a = rising_low(x, yt, 1n+iy, L.and_r(Nat.is_le(hi, iy), J.rising(yt, 1n+iy), ey), px)
          +b = asc_low(y, xt, ix, L.and_r(Nat.is_le(lo, ix), asc(xt, ix), ex), py)
          Empty.absurd({T.Appraisal.is_eq(x, y) == True{} : Bool}, L.lt_irrefl(iy, L.le_trans(1n+iy, ix, iy, a, b)))))

law not_pos_nil:
  for +x: T.Appraisal
  for +t: List<&2, T.Appraisal>
  for +e: {J.count(x, Nil{}) == J.count(x, x <> t) : Nat}
  Empty

law not_pos_nil.go:
  for -n: Nat
  for +e: {0n == n : Nat}
  for +p: {Nat.is_le(1n, n) == True{} : Bool}
  Empty

def not_pos_nil.go(n, e, p):
  L.ff(pos_move(n, 0n, Equal.sym(Nat, 0n, n, e), p))

def not_pos_nil(x, t, e):
  not_pos_nil.go(J.count(x, x <> t), e, pos_self(x, t))

law same_of_agree:
  for +xs: List<&2, T.Appraisal>
  for +ys: List<&2, T.Appraisal>
  for +lo: Nat
  for +hi: Nat
  for +ex: {asc(xs, lo) == True{} : Bool}
  for +ey: {J.rising(ys, hi) == True{} : Bool}
  for +ea: {agree(xs, xs, ys) == True{} : Bool}
  for +eb: {agree(ys, xs, ys) == True{} : Bool}
  {J.same(xs, ys) == True{} : Bool}

def same_of_agree(xs, ys, lo, hi, ex, ey, ea, eb):
  match xs ys:
    case Nil{} Nil{}:
      {==}
    case Nil{} y <> yt:
      Empty.absurd({J.same(Nil{}, y <> yt) == True{} : Bool},
        not_pos_nil(y, yt, agree_head(y, yt, Nil{}, y <> yt, eb)))
    case x <> xt Nil{}:
      Empty.absurd({J.same(x <> xt, Nil{}) == True{} : Bool},
        not_pos_nil(x, xt, Equal.sym(Nat, J.count(x, x <> xt), J.count(x, Nil{}), agree_head(x, xt, x <> xt, Nil{}, ea))))
    case x <> xt y <> yt:
      +ix = T.Appraisal.id(x)
      +iy = T.Appraisal.id(y)
      +cx = agree_head(x, xt, x <> xt, y <> yt, ea)
      +cy = agree_head(y, yt, x <> xt, y <> yt, eb)
      +he = heads_equal(x, xt, y, yt, lo, hi, ex, ey, cx, cy)
      +exy = app_of(x, y, he)
      same_cons.t(x, xt, y, yt, he,
        same_of_agree(xt, yt, ix, 1n+iy,
          L.and_r(Nat.is_le(lo, ix), asc(xt, ix), ex),
          L.and_r(Nat.is_le(hi, iy), J.rising(yt, 1n+iy), ey),
          agree_tail(xt, x, y, xt, yt, exy, agree_rest(x, xt, x <> xt, y <> yt, ea)),
          agree_tail(yt, x, y, xt, yt, exy, agree_rest(y, yt, x <> xt, y <> yt, eb))))

# agree survives sorting the left side.
law agree_sort:
  for +zs: List<&2, T.Appraisal>
  for +xs: List<&2, T.Appraisal>
  for +ys: List<&2, T.Appraisal>
  for +e: {agree(zs, xs, ys) == True{} : Bool}
  {agree(zs, J.sort(xs), ys) == True{} : Bool}

def agree_sort(zs, xs, ys, e):
  match zs:
    case Nil{}:
      {==}
    case +z <> t:
      L.and_i(Nat.is_eq(J.count(z, J.sort(xs)), J.count(z, ys)), agree(t, J.sort(xs), ys),
        L.is_eq_l(J.count(z, J.sort(xs)), J.count(z, xs), J.count(z, ys), count_sort(z, xs),
          L.and_l(Nat.is_eq(J.count(z, xs), J.count(z, ys)), agree(t, xs, ys), e)),
        agree_sort(t, xs, ys, agree_rest(z, t, xs, ys, e)))

# The checker's partition test passes for every list with the right counts.
law same_sort_intro:
  for +xs: List<&2, T.Appraisal>
  for +ys: List<&2, T.Appraisal>
  for +ey: {J.rising(ys, 0n) == True{} : Bool}
  for +ea: {agree(J.sort(xs), xs, ys) == True{} : Bool}
  for +eb: {agree(ys, xs, ys) == True{} : Bool}
  {J.same(J.sort(xs), ys) == True{} : Bool}

def same_sort_intro(xs, ys, ey, ea, eb):
  same_of_agree(J.sort(xs), ys, 0n, 0n, asc_sort(xs), ey,
    agree_sort(J.sort(xs), xs, ys, ea), agree_sort(ys, xs, ys, eb))

# And passing it means equal lists, so equal counts.
law same_eq:
  for +xs: List<&2, T.Appraisal>
  for +ys: List<&2, T.Appraisal>
  for +e: {J.same(xs, ys) == True{} : Bool}
  {xs == ys : List<&2, T.Appraisal>}

def same_eq(xs, ys, e):
  match xs ys:
    case Nil{} Nil{}:
      {==}
    case Nil{} y <> yt:
      L.never({Nil{} == y <> yt : List<&2, T.Appraisal>}, e)
    case x <> xt Nil{}:
      L.never({x <> xt == Nil{} : List<&2, T.Appraisal>}, e)
    case x <> xt y <> yt:
      +ee = T.Appraisal.is_eq(x, y)
      +es = J.same(xt, yt)
      %app_of(x, y, L.and_l(ee, es, e)) : {x <> xt == _ <> yt : List<&2, T.Appraisal>}
      %same_eq(xt, yt, L.and_r(ee, es, e)) : {x <> xt == x <> _ : List<&2, T.Appraisal>}
      {==}

law count_of_same:
  for +a: T.Appraisal
  for +xs: List<&2, T.Appraisal>
  for +ys: List<&2, T.Appraisal>
  for +e: {J.same(J.sort(xs), ys) == True{} : Bool}
  {J.count(a, xs) == J.count(a, ys) : Nat}

def count_of_same(a, xs, ys, e):
  Equal.trans(Nat, J.count(a, xs), J.count(a, J.sort(xs)), J.count(a, ys),
    Equal.sym(Nat, J.count(a, J.sort(xs)), J.count(a, xs), count_sort(a, xs)),
    %same_eq(J.sort(xs), ys, e) : {J.count(a, J.sort(xs)) == J.count(a, _) : Nat}
    {==})

# In a strictly rising list no appraisal appears twice.
law rising_once:
  for +a: T.Appraisal
  for +ys: List<&2, T.Appraisal>
  for +lo: Nat
  for +er: {J.rising(ys, lo) == True{} : Bool}
  {Nat.is_le(J.count(a, ys), 1n) == True{} : Bool}

def rising_once(a, ys, lo, er):
  match ys:
    case Nil{}:
      {==}
    case +h <> t:
      +ih = T.Appraisal.id(h)
      +ia = T.Appraisal.id(a)
      +c = J.count(a, t)
      +o = J.count.one(a, h)
      +rest = L.and_r(Nat.is_le(lo, ih), J.rising(t, 1n+ih), er)
      L.cases(T.Appraisal.is_eq(a, h), {Nat.is_le(Nat.add(o, c), 1n) == True{} : Bool},
        +e =>
          L.cases(Nat.is_le(1n, c), {Nat.is_le(Nat.add(o, c), 1n) == True{} : Bool},
            +p =>
              +low = rising_low(a, t, 1n+ih, rest, p)
              +low2 = {%Equal.sym(T.Appraisal, a, h, app_of(a, h, e)) : {Nat.is_le(1n+T.Appraisal.id(_), T.Appraisal.id(a)) == True{} : Bool}
                low : {Nat.is_le(1n+ia, ia) == True{} : Bool}}
              Empty.absurd({Nat.is_le(Nat.add(o, c), 1n) == True{} : Bool}, L.lt_irrefl(ia, low2)),
            +p => L.le_one(o, c, one_t(a, h, e), p)),
        +e => L.le_zero_add(o, c, one_f(a, h, e), rising_once(a, t, 1n+ih, rest)))

# Dropping and inserting
# ----------------------

law rising_mono:
  for +xs: List<&2, T.Appraisal>
  for +a: Nat
  for +b: Nat
  for +e: {J.rising(xs, b) == True{} : Bool}
  for +le: {Nat.is_le(a, b) == True{} : Bool}
  {J.rising(xs, a) == True{} : Bool}

def rising_mono(xs, a, b, e, le):
  match xs:
    case Nil{}:
      {==}
    case +h <> t:
      +ih = T.Appraisal.id(h)
      L.and_i(Nat.is_le(a, ih), J.rising(t, 1n+ih),
        L.le_trans(a, b, ih, le, L.and_l(Nat.is_le(b, ih), J.rising(t, 1n+ih), e)),
        L.and_r(Nat.is_le(b, ih), J.rising(t, 1n+ih), e))

law rising_put:
  for +c: Bool
  for +h: T.Appraisal
  for +rest: List<&2, T.Appraisal>
  for +lo: Nat
  for +e1: {Nat.is_le(lo, T.Appraisal.id(h)) == True{} : Bool}
  for +e2: {J.rising(rest, 1n+T.Appraisal.id(h)) == True{} : Bool}
  {J.rising(J.without.put(c, h, rest), lo) == True{} : Bool}

def rising_put(c, h, rest, lo, e1, e2):
  match c:
    case True{}:
      rising_mono(rest, lo, 1n+T.Appraisal.id(h), e2, L.le_trans(lo, T.Appraisal.id(h), 1n+T.Appraisal.id(h), e1, L.le_step(T.Appraisal.id(h))))
    case False{}:
      L.and_i(Nat.is_le(lo, T.Appraisal.id(h)), J.rising(rest, 1n+T.Appraisal.id(h)), e1, e2)

law rising_without:
  for +xs: List<&2, T.Appraisal>
  for +i: Nat
  for +lo: Nat
  for +e: {J.rising(xs, lo) == True{} : Bool}
  {J.rising(J.without(xs, i), lo) == True{} : Bool}

def rising_without(xs, i, lo, e):
  match xs:
    case Nil{}:
      {==}
    case +h <> t:
      +ih = T.Appraisal.id(h)
      rising_put(Nat.is_eq(ih, i), h, J.without(t, i), lo, L.and_l(Nat.is_le(lo, ih), J.rising(t, 1n+ih), e),
        rising_without(t, i, 1n+ih, L.and_r(Nat.is_le(lo, ih), J.rising(t, 1n+ih), e)))

law id_of_eq:
  for +a: T.Appraisal
  for +b: T.Appraisal
  for +e: {T.Appraisal.is_eq(a, b) == True{} : Bool}
  {T.Appraisal.id(a) == T.Appraisal.id(b) : Nat}

def id_of_eq(a, b, e):
  %app_of(a, b, e) : {T.Appraisal.id(a) == T.Appraisal.id(_) : Nat}
  {==}

# Appraisals on opposite sides of an id test can't be equal.
law one_zero.same:
  for +z: T.Appraisal
  for +h: T.Appraisal
  for +i: Nat
  for +ez: {Nat.is_eq(T.Appraisal.id(z), i) == True{} : Bool}
  for +eh: {Nat.is_eq(T.Appraisal.id(h), i) == False{} : Bool}
  {J.count.one(z, h) == 0n : Nat}

def one_zero.same(z, h, i, ez, eh):
  L.cases(T.Appraisal.is_eq(z, h), {J.count.one(z, h) == 0n : Nat},
    +e =>
      L.clash(Nat.is_eq(T.Appraisal.id(h), i), {J.count.one(z, h) == 0n : Nat},
        L.is_eq_l(T.Appraisal.id(h), T.Appraisal.id(z), i, Equal.sym(Nat, T.Appraisal.id(z), T.Appraisal.id(h), id_of_eq(z, h, e)), ez),
        eh),
    +e => one_f(z, h, e))

law one_zero.other:
  for +z: T.Appraisal
  for +h: T.Appraisal
  for +i: Nat
  for +ez: {Nat.is_eq(T.Appraisal.id(z), i) == False{} : Bool}
  for +eh: {Nat.is_eq(T.Appraisal.id(h), i) == True{} : Bool}
  {J.count.one(z, h) == 0n : Nat}

def one_zero.other(z, h, i, ez, eh):
  L.cases(T.Appraisal.is_eq(z, h), {J.count.one(z, h) == 0n : Nat},
    +e =>
      L.clash(Nat.is_eq(T.Appraisal.id(z), i), {J.count.one(z, h) == 0n : Nat},
        L.is_eq_l(T.Appraisal.id(z), T.Appraisal.id(h), i, id_of_eq(z, h, e), eh),
        ez),
    +e => one_f(z, h, e))

law cw_same:
  for +c: Bool
  for +z: T.Appraisal
  for +h: T.Appraisal
  for +rest: List<&2, T.Appraisal>
  for +i: Nat
  for +ec: {Nat.is_eq(T.Appraisal.id(h), i) == c : Bool}
  for +ez: {Nat.is_eq(T.Appraisal.id(z), i) == True{} : Bool}
  for +ih: {J.count(z, rest) == 0n : Nat}
  {J.count(z, J.without.put(c, h, rest)) == 0n : Nat}

def cw_same(c, z, h, rest, i, ec, ez, ih):
  match c:
    case True{}:
      ih
    case False{}:
      L.add_both_zero(J.count.one(z, h), J.count(z, rest), one_zero.same(z, h, i, ez, ec), ih)

law count_without_same:
  for +z: T.Appraisal
  for +xs: List<&2, T.Appraisal>
  for +i: Nat
  for +ez: {Nat.is_eq(T.Appraisal.id(z), i) == True{} : Bool}
  {J.count(z, J.without(xs, i)) == 0n : Nat}

def count_without_same(z, xs, i, ez):
  match xs:
    case Nil{}:
      {==}
    case +h <> t:
      cw_same(Nat.is_eq(T.Appraisal.id(h), i), z, h, J.without(t, i), i, {==}, ez, count_without_same(z, t, i, ez))

law cw_other:
  for +c: Bool
  for +z: T.Appraisal
  for +h: T.Appraisal
  for +rest: List<&2, T.Appraisal>
  for +t: List<&2, T.Appraisal>
  for +i: Nat
  for +ec: {Nat.is_eq(T.Appraisal.id(h), i) == c : Bool}
  for +ez: {Nat.is_eq(T.Appraisal.id(z), i) == False{} : Bool}
  for +ih: {J.count(z, rest) == J.count(z, t) : Nat}
  {J.count(z, J.without.put(c, h, rest)) == J.count(z, h <> t) : Nat}

def cw_other(c, z, h, rest, t, i, ec, ez, ih):
  match c:
    case True{}:
      %Equal.sym(Nat, J.count.one(z, h), 0n, one_zero.other(z, h, i, ez, ec)) : {J.count(z, rest) == Nat.add(_, J.count(z, t)) : Nat}
      ih
    case False{}:
      L.add_r(J.count.one(z, h), J.count(z, rest), J.count(z, t), ih)

law count_without_other:
  for +z: T.Appraisal
  for +xs: List<&2, T.Appraisal>
  for +i: Nat
  for +ez: {Nat.is_eq(T.Appraisal.id(z), i) == False{} : Bool}
  {J.count(z, J.without(xs, i)) == J.count(z, xs) : Nat}

def count_without_other(z, xs, i, ez):
  match xs:
    case Nil{}:
      {==}
    case +h <> t:
      cw_other(Nat.is_eq(T.Appraisal.id(h), i), z, h, J.without(t, i), t, i, {==}, ez, count_without_other(z, t, i, ez))

law insert_t:
  for +h: T.Appraisal
  for +t: List<&2, T.Appraisal>
  for +j: T.Appraisal
  for +e: {Nat.is_le(T.Appraisal.id(j), T.Appraisal.id(h)) == True{} : Bool}
  {J.insert(h <> t, j) == j <> h <> t : List<&2, T.Appraisal>}

def insert_t(h, t, j, e):
  %Equal.sym(Bool, Nat.is_le(T.Appraisal.id(j), T.Appraisal.id(h)), True{}, e) : {J.lazy(_, u => j <> h <> t, u => h <> J.insert(t, j)) == j <> h <> t : List<&2, T.Appraisal>}
  {==}

law insert_f:
  for +h: T.Appraisal
  for +t: List<&2, T.Appraisal>
  for +j: T.Appraisal
  for +e: {Nat.is_le(T.Appraisal.id(j), T.Appraisal.id(h)) == False{} : Bool}
  {J.insert(h <> t, j) == h <> J.insert(t, j) : List<&2, T.Appraisal>}

def insert_f(h, t, j, e):
  %Equal.sym(Bool, Nat.is_le(T.Appraisal.id(j), T.Appraisal.id(h)), False{}, e) : {J.lazy(_, u => j <> h <> t, u => h <> J.insert(t, j)) == h <> J.insert(t, j) : List<&2, T.Appraisal>}
  {==}

law count_insert:
  for +z: T.Appraisal
  for +xs: List<&2, T.Appraisal>
  for +j: T.Appraisal
  {J.count(z, J.insert(xs, j)) == Nat.add(J.count.one(z, j), J.count(z, xs)) : Nat}

def count_insert(z, xs, j):
  match xs:
    case Nil{}:
      {==}
    case +h <> t:
      +ih = T.Appraisal.id(h)
      +ij = T.Appraisal.id(j)
      L.cases(Nat.is_le(ij, ih), {J.count(z, J.insert(h <> t, j)) == Nat.add(J.count.one(z, j), J.count(z, h <> t)) : Nat},
        +e =>
          %Equal.sym(List<&2, T.Appraisal>, J.insert(h <> t, j), j <> h <> t, insert_t(h, t, j, e)) : {J.count(z, _) == Nat.add(J.count.one(z, j), J.count(z, h <> t)) : Nat}
          {==},
        +e =>
          %Equal.sym(List<&2, T.Appraisal>, J.insert(h <> t, j), h <> J.insert(t, j), insert_f(h, t, j, e)) : {J.count(z, _) == Nat.add(J.count.one(z, j), J.count(z, h <> t)) : Nat}
          L.swap_step(J.count.one(z, h), J.count(z, J.insert(t, j)), J.count.one(z, j), J.count(z, t), count_insert(z, t, j)))

law rising_insert:
  for +xs: List<&2, T.Appraisal>
  for +j: T.Appraisal
  for +lo: Nat
  for +er: {J.rising(xs, lo) == True{} : Bool}
  for +el: {Nat.is_le(lo, T.Appraisal.id(j)) == True{} : Bool}
  for +ef: {J.has_id(xs, T.Appraisal.id(j)) == False{} : Bool}
  {J.rising(J.insert(xs, j), lo) == True{} : Bool}

def rising_insert(xs, j, lo, er, el, ef):
  match xs:
    case Nil{}:
      L.and_i(Nat.is_le(lo, T.Appraisal.id(j)), True{}, el, {==})
    case +h <> t:
      +ih = T.Appraisal.id(h)
      +ij = T.Appraisal.id(j)
      +ne = L.or_l(Nat.is_eq(ih, ij), J.has_id(t, ij), ef)
      +ft = L.or_r(Nat.is_eq(ih, ij), J.has_id(t, ij), ef)
      +lh = L.and_l(Nat.is_le(lo, ih), J.rising(t, 1n+ih), er)
      +rt = L.and_r(Nat.is_le(lo, ih), J.rising(t, 1n+ih), er)
      L.cases(Nat.is_le(ij, ih), {J.rising(J.insert(h <> t, j), lo) == True{} : Bool},
        +e =>
          %Equal.sym(List<&2, T.Appraisal>, J.insert(h <> t, j), j <> h <> t, insert_t(h, t, j, e)) : {J.rising(_, lo) == True{} : Bool}
          L.and_i(Nat.is_le(lo, ij), J.rising(h <> t, 1n+ij), el,
            L.and_i(Nat.is_le(1n+ij, ih), J.rising(t, 1n+ih), L.lt_of_le_ne(ij, ih, e, ne), rt)),
        +e =>
          %Equal.sym(List<&2, T.Appraisal>, J.insert(h <> t, j), h <> J.insert(t, j), insert_f(h, t, j, e)) : {J.rising(_, lo) == True{} : Bool}
          L.and_i(Nat.is_le(lo, ih), J.rising(J.insert(t, j), 1n+ih), lh,
            rising_insert(t, j, 1n+ih, rt, L.le_total(ij, ih, e), ft)))

# States
# ------

law in_state_put:
  for +c: Bool
  for +a: T.Appraisal
  for +r: List<&2, T.Appraisal>
  for +s: Nat
  for +ea: {Nat.is_eq(T.Appraisal.state(a), s) == True{} : Bool}
  for +er: {J.in_state(r, s) == True{} : Bool}
  {J.in_state(J.without.put(c, a, r), s) == True{} : Bool}

def in_state_put(c, a, r, s, ea, er):
  match c:
    case True{}:
      er
    case False{}:
      L.and_i(Nat.is_eq(T.Appraisal.state(a), s), J.in_state(r, s), ea, er)

law in_state_without:
  for +xs: List<&2, T.Appraisal>
  for +i: Nat
  for +s: Nat
  for +e: {J.in_state(xs, s) == True{} : Bool}
  {J.in_state(J.without(xs, i), s) == True{} : Bool}

def in_state_without(xs, i, s, e):
  match xs:
    case Nil{}:
      {==}
    case +h <> +t:
      +x = Nat.is_eq(T.Appraisal.state(h), s)
      +y = J.in_state(t, s)
      in_state_put(Nat.is_eq(T.Appraisal.id(h), i), h, J.without(t, i), s, L.and_l(x, y, e),
        in_state_without(t, i, s, L.and_r(x, y, e)))

law in_state_insert:
  for +xs: List<&2, T.Appraisal>
  for +j: T.Appraisal
  for +s: Nat
  for +ex: {J.in_state(xs, s) == True{} : Bool}
  for +ej: {Nat.is_eq(T.Appraisal.state(j), s) == True{} : Bool}
  {J.in_state(J.insert(xs, j), s) == True{} : Bool}

def in_state_insert(xs, j, s, ex, ej):
  match xs:
    case Nil{}:
      L.and_i(Nat.is_eq(T.Appraisal.state(j), s), True{}, ej, {==})
    case +h <> +t:
      +x = Nat.is_eq(T.Appraisal.state(h), s)
      +y = J.in_state(t, s)
      L.cases(Nat.is_le(T.Appraisal.id(j), T.Appraisal.id(h)), {J.in_state(J.insert(h <> t, j), s) == True{} : Bool},
        +e =>
          %Equal.sym(List<&2, T.Appraisal>, J.insert(h <> t, j), j <> h <> t, insert_t(h, t, j, e)) : {J.in_state(_, s) == True{} : Bool}
          L.and_i(Nat.is_eq(T.Appraisal.state(j), s), J.in_state(h <> t, s), ej, ex),
        +e =>
          %Equal.sym(List<&2, T.Appraisal>, J.insert(h <> t, j), h <> J.insert(t, j), insert_f(h, t, j, e)) : {J.in_state(_, s) == True{} : Bool}
          L.and_i(x, J.in_state(J.insert(t, j), s), L.and_l(x, y, ex),
            in_state_insert(t, j, s, L.and_r(x, y, ex), ej)))

law count_skip:
  for +a: T.Appraisal
  for +h: T.Appraisal
  for +t: List<&2, T.Appraisal>
  for +e: {T.Appraisal.is_eq(a, h) == False{} : Bool}
  {J.count(a, h <> t) == J.count(a, t) : Nat}

def count_skip(a, h, t, e):
  %Equal.sym(Nat, J.count.one(a, h), 0n, one_f(a, h, e)) : {Nat.add(_, J.count(a, t)) == J.count(a, t) : Nat}
  {==}

# Anything counted in a list that's all in one state is in that state.
law state_of_count:
  for +a: T.Appraisal
  for +xs: List<&2, T.Appraisal>
  for +s: Nat
  for +ex: {J.in_state(xs, s) == True{} : Bool}
  for +ec: {Nat.is_le(1n, J.count(a, xs)) == True{} : Bool}
  {T.Appraisal.state(a) == s : Nat}

def state_of_count(a, xs, s, ex, ec):
  match xs:
    case Nil{}:
      L.never({T.Appraisal.state(a) == s : Nat}, ec)
    case +h <> +t:
      +x = Nat.is_eq(T.Appraisal.state(h), s)
      +y = J.in_state(t, s)
      L.cases(T.Appraisal.is_eq(a, h), {T.Appraisal.state(a) == s : Nat},
        +e =>
          %Equal.sym(T.Appraisal, a, h, app_of(a, h, e)) : {T.Appraisal.state(_) == s : Nat}
          L.eq_of(T.Appraisal.state(h), s, L.and_l(x, y, ex)),
        +e =>
          state_of_count(a, t, s, L.and_r(x, y, ex),
            %count_skip(a, h, t, e) : {Nat.is_le(1n, _) == True{} : Bool}
            ec))

# take: what's found plus what's left is the whole list
def FC(+z: T.Appraisal, m: Maybe<&2, T.Appraisal>) -> Nat:
  match m:
    case None{}:
      0n
    case Some{j}:
      J.count.one(z, j)

law take_cons_found:
  for +h: T.Appraisal
  for +r: J.Taken
  {J.Taken.found(J.Taken.cons(h, r)) == J.Taken.found(r) : Maybe<&2, T.Appraisal>}

def take_cons_found(h, r):
  match r:
    case J.Taken{f, x}:
      {==}

law take_cons_rest:
  for +h: T.Appraisal
  for +r: J.Taken
  {J.Taken.rest(J.Taken.cons(h, r)) == h <> J.Taken.rest(r) : List<&2, T.Appraisal>}

def take_cons_rest(h, r):
  match r:
    case J.Taken{f, x}:
      {==}

law take_step:
  for +c: Bool
  for +z: T.Appraisal
  for +h: T.Appraisal
  for +t: List<&2, T.Appraisal>
  for +r: J.Taken
  for +ih: {J.count(z, t) == Nat.add(FC(z, J.Taken.found(r)), J.count(z, J.Taken.rest(r))) : Nat}
  {J.count(z, h <> t) == Nat.add(FC(z, J.Taken.found(J.take.if(c, h, t, r))), J.count(z, J.Taken.rest(J.take.if(c, h, t, r)))) : Nat}

def take_step(c, z, h, t, r, ih):
  match c:
    case True{}:
      {==}
    case False{}:
      +q = J.Taken.cons(h, r)
      +o = J.count.one(z, h)
      %Equal.sym(Maybe<&2, T.Appraisal>, J.Taken.found(q), J.Taken.found(r), take_cons_found(h, r)) : {Nat.add(o, J.count(z, t)) == Nat.add(FC(z, _), J.count(z, J.Taken.rest(q))) : Nat}
      %Equal.sym(List<&2, T.Appraisal>, J.Taken.rest(q), h <> J.Taken.rest(r), take_cons_rest(h, r)) : {Nat.add(o, J.count(z, t)) == Nat.add(FC(z, J.Taken.found(r)), J.count(z, _)) : Nat}
      L.swap_step(o, J.count(z, t), FC(z, J.Taken.found(r)), J.count(z, J.Taken.rest(r)), ih)

law take_count:
  for +z: T.Appraisal
  for +xs: List<&2, T.Appraisal>
  for +i: Nat
  {J.count(z, xs) == Nat.add(FC(z, J.Taken.found(J.take(xs, i))), J.count(z, J.Taken.rest(J.take(xs, i)))) : Nat}

def take_count(z, xs, i):
  match xs:
    case Nil{}:
      {==}
    case +h <> t:
      take_step(Nat.is_eq(T.Appraisal.id(h), i), z, h, t, J.take(t, i), take_count(z, t, i))
