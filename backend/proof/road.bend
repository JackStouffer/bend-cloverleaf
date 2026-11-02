import Base
import ../road/spec.bend as Sp
import ../road/search.bend as S
import ../road/path.bend as Pa
import ../road/lanes.bend as Lanes
import ./logic.bend as L

# Facts about reading arrays, and the road laws built on them.
#
# An array can't be copied, and evidence has to come from live code, so a proof
# can't simply read the same array twice. Everything here is built on `copy`: the
# Base clone gives two live arrays that are provably the original, and `reads`
# uses it to hand back each word with its evidence, plus a live copy to carry on
# with. That threads an array through a proof the way the code threads it.

def Copies(-a: Array<U32>) -> Type:
  &b: Array<U32> -> &c: Array<U32> -> {b == a : Array<U32>} & {c == a : Array<U32>}

law copy.same:
  for -xs: Array<U32>
  for -ys: Array<U32>
  for -b: Array<U32>
  for -c: Array<U32>
  for +e: {b == xs : Array<U32>}
  for +f: {c == ys : Array<U32>}
  {ANode{b, c} == ANode{xs, ys} : Array<U32>}

def copy.same(xs, ys, b, c, e, f):
  %e : {ANode{b, c} == ANode{_, ys} : Array<U32>}
  %f : {ANode{b, c} == ANode{b, _} : Array<U32>}
  {==}

def copy.node(-xs: Array<U32>, -ys: Array<U32>, l: Copies(xs), r: Copies(ys)) -> Copies(ANode{xs, ys}):
  (b1, c1, e1, f1) = l
  (b2, c2, e2, f2) = r
  (ANode{b1, b2}, ANode{c1, c2}, copy.same(xs, ys, b1, b2, e1, e2), copy.same(xs, ys, c1, c2, f1, f2))

def copy(a: Array<U32>) -> Copies(a):
  match a:
    case ALeaf{+x}:
      (ALeaf{x}, ALeaf{x}, {==}, {==})
    case ANode{xs, ys}:
      copy.node(xs, ys, copy(xs), copy(ys))

# A read is the array back and a word
# -----------------------------------

def Sized(-a: Array<U32>) -> Type:
  &n: U32 -> {(a, n) == Array.size(U32, a) : Array<U32> & U32}

law size.same:
  for -xs: Array<U32>
  for -ys: Array<U32>
  for +n: U32
  for +e: {(xs, n) == Array.size(U32, xs) : Array<U32> & U32}
  {(ANode{xs, ys}, U32.shl(n)) == Array.size.node(U32, ys, Array.size(U32, xs)) : Array<U32> & U32}

def size.same(xs, ys, n, e):
  %e : {(ANode{xs, ys}, U32.shl(n)) == Array.size.node(U32, ys, _) : Array<U32> & U32}
  {==}

def size.pair(-xs: Array<U32>, -ys: Array<U32>, +n: U32, +e: {(xs, n) == Array.size(U32, xs) : Array<U32> & U32}) -> Sized(ANode{xs, ys}):
  (U32.shl(n), size.same(xs, ys, n, e))

def size.node(-xs: Array<U32>, -ys: Array<U32>, r: Sized(xs)) -> Sized(ANode{xs, ys}):
  (n, e) = r
  size.pair(xs, ys, n, e)

def size(a: Array<U32>) -> Sized(a):
  match a:
    case ALeaf{+x}:
      (1, {==})
    case ANode{xs, ys}:
      size.node(xs, ys, size(xs))

# Reading down the tree.
def Got(-a: Array<U32>, +n: U32, +i: U32, -z: Bool) -> Type:
  &v: U32 -> {(a, v) == Array.get.go(U32, a, n, i, z) : Array<U32> & U32}

law get.lo:
  for -xs: Array<U32>
  for -ys: Array<U32>
  for +v: U32
  for -p: Array<U32> & U32
  for +e: {(xs, v) == p : Array<U32> & U32}
  {(ANode{xs, ys}, v) == Array.swap.lo(U32, ys, p) : Array<U32> & U32}

def get.lo(xs, ys, v, p, e):
  %e : {(ANode{xs, ys}, v) == Array.swap.lo(U32, ys, _) : Array<U32> & U32}
  {==}

law get.hi:
  for -xs: Array<U32>
  for -ys: Array<U32>
  for +v: U32
  for -p: Array<U32> & U32
  for +e: {(ys, v) == p : Array<U32> & U32}
  {(ANode{xs, ys}, v) == Array.swap.hi(U32, xs, p) : Array<U32> & U32}

def get.hi(xs, ys, v, p, e):
  %e : {(ANode{xs, ys}, v) == Array.swap.hi(U32, xs, _) : Array<U32> & U32}
  {==}

def got.lo.pair(-xs: Array<U32>, -ys: Array<U32>, +h: U32, +i: U32, +v: U32, +e: {(xs, v) == Array.get.go(U32, xs, h, i, U32.is_lt(i, U32.shr(h))) : Array<U32> & U32}) -> &v: U32 -> {(ANode{xs, ys}, v) == Array.swap.lo(U32, ys, Array.get.go(U32, xs, h, i, U32.is_lt(i, U32.shr(h)))) : Array<U32> & U32}:
  (v, get.lo(xs, ys, v, Array.get.go(U32, xs, h, i, U32.is_lt(i, U32.shr(h))), e))

def got.lo(-xs: Array<U32>, -ys: Array<U32>, +n: U32, +h: U32, +i: U32, r: Got(xs, h, i, U32.is_lt(i, U32.shr(h)))) -> &v: U32 -> {(ANode{xs, ys}, v) == Array.swap.lo(U32, ys, Array.get.go(U32, xs, h, i, U32.is_lt(i, U32.shr(h)))) : Array<U32> & U32}:
  (v, e) = r
  got.lo.pair(xs, ys, h, i, v, e)

def got.hi.pair(-xs: Array<U32>, -ys: Array<U32>, +h: U32, +j: U32, +v: U32, +e: {(ys, v) == Array.get.go(U32, ys, h, j, U32.is_lt(j, U32.shr(h))) : Array<U32> & U32}) -> &v: U32 -> {(ANode{xs, ys}, v) == Array.swap.hi(U32, xs, Array.get.go(U32, ys, h, j, U32.is_lt(j, U32.shr(h)))) : Array<U32> & U32}:
  (v, get.hi(xs, ys, v, Array.get.go(U32, ys, h, j, U32.is_lt(j, U32.shr(h))), e))

def got.hi(-xs: Array<U32>, -ys: Array<U32>, +n: U32, +h: U32, +j: U32, r: Got(ys, h, j, U32.is_lt(j, U32.shr(h)))) -> &v: U32 -> {(ANode{xs, ys}, v) == Array.swap.hi(U32, xs, Array.get.go(U32, ys, h, j, U32.is_lt(j, U32.shr(h)))) : Array<U32> & U32}:
  (v, e) = r
  got.hi.pair(xs, ys, h, j, v, e)

def got(a: Array<U32>, +n: U32, +i: U32, z: Bool) -> Got(a, n, i, z):
  match a z:
    case ALeaf{+x} _:
      (x, {==})
    case ANode{xs, ys} True{}:
      +h = U32.shr(n)
      got.lo(xs, ys, n, h, i, got(xs, h, i, U32.is_lt(i, U32.shr(h))))
    case ANode{xs, ys} False{}:
      +h = U32.shr(n)
      +j = U32.sub(i, h)
      got.hi(xs, ys, n, h, j, got(ys, h, j, U32.is_lt(j, U32.shr(h))))

def Read(-a: Array<U32>, +i: U32) -> Type:
  &v: U32 -> {(a, v) == Array.get(U32, a, i) : Array<U32> & U32}

law read.same:
  for -a: Array<U32>
  for -b: Array<U32>
  for -c: Array<U32>
  for +i: U32
  for +n: U32
  for +v: U32
  for +e1: {b == a : Array<U32>}
  for +e2: {c == a : Array<U32>}
  for +es: {(b, n) == Array.size(U32, b) : Array<U32> & U32}
  for +eg: {(c, v) == Array.get.go(U32, c, n, U32.and(i, U32.sub(n, 1)), U32.is_lt(U32.and(i, U32.sub(n, 1)), U32.shr(n))) : Array<U32> & U32}
  {(a, v) == Array.get(U32, a, i) : Array<U32> & U32}

def read.same(a, b, c, i, n, v, e1, e2, es, eg):
  %e1 : {(a, v) == Array.get.at(U32, i, Array.size(U32, _)) : Array<U32> & U32}
  %es : {(a, v) == Array.get.at(U32, i, _) : Array<U32> & U32}
  %Equal.trans(Array<U32>, c, a, b, e2, Equal.sym(Array<U32>, b, a, e1)) : {(a, v) == Array.get.go(U32, _, n, U32.and(i, U32.sub(n, 1)), U32.is_lt(U32.and(i, U32.sub(n, 1)), U32.shr(n))) : Array<U32> & U32}
  %e2 : {(_, v) == Array.get.go(U32, c, n, U32.and(i, U32.sub(n, 1)), U32.is_lt(U32.and(i, U32.sub(n, 1)), U32.shr(n))) : Array<U32> & U32}
  eg

def read.pair(-a: Array<U32>, -b: Array<U32>, -c: Array<U32>, +i: U32, +n: U32, +v: U32, +e1: {b == a : Array<U32>}, +e2: {c == a : Array<U32>}, +es: {(b, n) == Array.size(U32, b) : Array<U32> & U32}, +eg: {(c, v) == Array.get.go(U32, c, n, U32.and(i, U32.sub(n, 1)), U32.is_lt(U32.and(i, U32.sub(n, 1)), U32.shr(n))) : Array<U32> & U32}) -> Read(a, i):
  (v, read.same(a, b, c, i, n, v, e1, e2, es, eg))

def read.got(-a: Array<U32>, -b: Array<U32>, -c: Array<U32>, +i: U32, +n: U32, +e1: {b == a : Array<U32>}, +e2: {c == a : Array<U32>}, +es: {(b, n) == Array.size(U32, b) : Array<U32> & U32}, r: Got(c, n, U32.and(i, U32.sub(n, 1)), U32.is_lt(U32.and(i, U32.sub(n, 1)), U32.shr(n)))) -> Read(a, i):
  (v, eg) = r
  read.pair(a, b, c, i, n, v, e1, e2, es, eg)

def read.go(-a: Array<U32>, -b: Array<U32>, c: Array<U32>, +i: U32, +n: U32, +e1: {b == a : Array<U32>}, +e2: {c == a : Array<U32>}, +es: {(b, n) == Array.size(U32, b) : Array<U32> & U32}) -> Read(a, i):
  +j = U32.and(i, U32.sub(n, 1))
  read.got(a, b, c, i, n, e1, e2, es, got(c, n, j, U32.is_lt(j, U32.shr(n))))

def read.sized(-a: Array<U32>, -b: Array<U32>, c: Array<U32>, +i: U32, +e1: {b == a : Array<U32>}, +e2: {c == a : Array<U32>}, s: Sized(b)) -> Read(a, i):
  (n, es) = s
  read.go(a, b, c, i, n, e1, e2, es)

def read.copies(-a: Array<U32>, +i: U32, l: Copies(a)) -> Read(a, i):
  (b, c, e1, e2) = l
  read.sized(a, b, c, i, e1, e2, size(b))

# The one fact every proof below rests on: a read hands back the same array, and
# the word it hands back is At's.
def read(a: Array<U32>, +i: U32) -> Read(a, i):
  read.copies(a, i, copy(a))

# Several reads
# -------------

# The word at each index with its evidence, then a live copy of the array.
def Reads(ids: List<&2, U32>, -a: Array<U32>) -> Type:
  match ids:
    case Nil{}:
      &h: Array<U32> -> {h == a : Array<U32>}
    case +i <> t:
      &v: U32 -> {(a, v) == Array.get(U32, a, i) : Array<U32> & U32} & Reads(t, a)

law read.as:
  for -a: Array<U32>
  for -b: Array<U32>
  for +i: U32
  for +v: U32
  for +e: {b == a : Array<U32>}
  for +r: {(b, v) == Array.get(U32, b, i) : Array<U32> & U32}
  {(a, v) == Array.get(U32, a, i) : Array<U32> & U32}

def read.as(a, b, i, v, e, r):
  %e : {(_, v) == Array.get(U32, _, i) : Array<U32> & U32}
  r

def reads.more(-a: Array<U32>, -b: Array<U32>, +i: U32, -t: List<&2, U32>, +v: U32, +e: {b == a : Array<U32>}, +r: {(b, v) == Array.get(U32, b, i) : Array<U32> & U32}, more: Reads(t, a)) -> Reads(i <> t, a):
  (v, (read.as(a, b, i, v, e, r), more))

def reads.pair(-a: Array<U32>, -b: Array<U32>, +i: U32, -t: List<&2, U32>, +e: {b == a : Array<U32>}, r: Read(b, i), more: Reads(t, a)) -> Reads(i <> t, a):
  (v, ev) = r
  reads.more(a, b, i, t, v, e, ev, more)

law reads.on:
  for -a: Array<U32>
  for -c: Array<U32>
  for +t: List<&2, U32>
  for +e: {c == a : Array<U32>}
  for more: Reads(t, c)
  Reads(t, a)

def reads.on(a, c, t, e, more):
  %e : Reads(t, _)
  more

def reads.copies(-a: Array<U32>, +i: U32, +t: List<&2, U32>, l: Copies(a), rest: (@c: Array<U32> -> Reads(t, c))) -> Reads(i <> t, a):
  (b, c, e1, e2) = l
  reads.pair(a, b, i, t, e1, read(b, i), reads.on(a, c, t, e2, rest(c)))

def reads(ids: List<&2, U32>, a: Array<U32>) -> Reads(ids, a):
  match ids:
    case Nil{}:
      (a, {==})
    case +i <> +t:
      reads.copies(a, i, t, copy(a), c => reads(t, c))

# Paths
# -----

def Val(+m: Maybe<&2, Nat>) -> Nat:
  match m:
    case None{}:
      0n
    case Some{+x}:
      x

law some.inj:
  for +a: Nat
  for +b: Nat
  for +e: {Some{a} == Some{b} : Maybe<&2, Nat>}
  {a == b : Nat}

def some.inj(a, b, e):
  %e : {Val(Some{a}) == Val(_) : Nat}
  {==}

def IsNone(+m: Maybe<&2, Nat>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{_}:
      Empty

law none.empty:
  for +c: Nat
  for +e: {None{} == Some{c} : Maybe<&2, Nat>}
  Empty

def none.empty(c, e):
  %e : IsNone(_)
  Unit{}

law none.some:
  for +c: Nat
  for -A: Type
  for +e: {None{} == Some{c} : Maybe<&2, Nat>}
  A

def none.some(c, A, e):
  Empty.absurd(A, none.empty(c, e))

# A walk's cost reached Some, so it ended on dst and the total is that cost.
law end.sound:
  for +b: Bool
  for -g: Array<U32>
  for +total: Nat
  for +c: Nat
  for +e: {Pa.Walked.cost(Pa.Path.end.at(b, g, total)) == Some{c} : Maybe<&2, Nat>}
  {b == True{} : Bool} & {total == c : Nat}

def end.sound(b, g, total, c, e):
  match b:
    case True{}:
      ({==}, some.inj(total, c, e))
    case False{}:
      none.some(c, {False{} == True{} : Bool} & {total == c : Nat}, e)

# Once a walk fails it never moves again.
law walk.false:
  for +xs: List<&2, U32>
  for -g: Array<U32>
  for +n: U32
  for +at: U32
  for +total: Nat
  {Pa.Path.walk(xs, Pa.Hop{g, at, total, False{}}, n) == Pa.Hop{g, at, total, False{}} : Pa.Hop}

def walk.false(xs, g, n, at, total):
  match xs:
    case Nil{}:
      {==}
    case +a <> t:
      walk.false(t, g, n, at, total)

def Arc.ids(+n: U32, +a: U32, +at: U32) -> List<&2, U32>:
  [(at + 2 : U32), (at + 3 : U32), (n + (2 * a : U32) + 4 : U32), (n + (2 * a : U32) + 5 : U32)]

def Ok(+n: U32, +at: U32, +lo: U32, +a: U32, +hi: U32) -> Bool:
  U32.is_lt(at, n) && U32.is_le(lo, a) && U32.is_lt(a, hi)

def Ends(xs: List<&2, U32>, -g: Array<U32>, +n: U32, +at: U32, +dst: U32, +total: Nat, +c: Nat) -> Data:
  {Pa.Walked.cost(Pa.Path.end(Pa.Path.walk(xs, Pa.Hop{g, at, total, True{}}, n), dst)) == Some{c} : Maybe<&2, Nat>}

law at.is:
  for -a: Array<U32>
  for +i: U32
  for +v: U32
  for +e: {(a, v) == Array.get(U32, a, i) : Array<U32> & U32}
  {v == Sp.At(a, i) : U32}

def at.is(a, i, v, e):
  %e : {v == Sp.Snd(_) : U32}
  {==}

law hop.yes:
  for -g: Array<U32>
  for +n: U32
  for +a: U32
  for +at: U32
  for +total: Nat
  for +lo: U32
  for +hi: U32
  for +head: U32
  for +cost: U32
  for +el: {(g, lo) == Array.get(U32, g, (at + 2 : U32)) : Array<U32> & U32}
  for +eh: {(g, hi) == Array.get(U32, g, (at + 3 : U32)) : Array<U32> & U32}
  for +ed: {(g, head) == Array.get(U32, g, (n + (2 * a : U32) + 4 : U32)) : Array<U32> & U32}
  for +ec: {(g, cost) == Array.get(U32, g, (n + (2 * a : U32) + 5 : U32)) : Array<U32> & U32}
  for +ok: {Ok(n, at, lo, a, hi) == True{} : Bool}
  {Pa.Hop.go(True{}, g, n, a, at, total) == Pa.Hop{g, head, Nat.add(total, U32.to_nat(cost)), True{}} : Pa.Hop}

def hop.yes(g, n, a, at, total, lo, hi, head, cost, el, eh, ed, ec, ok):
  %el : {Pa.Hop.lo(_, n, a, at, total) == Pa.Hop{g, head, Nat.add(total, U32.to_nat(cost)), True{}} : Pa.Hop}
  %eh : {Pa.Hop.hi(_, lo, n, a, at, total) == Pa.Hop{g, head, Nat.add(total, U32.to_nat(cost)), True{}} : Pa.Hop}
  %Equal.sym(Bool, Ok(n, at, lo, a, hi), True{}, ok) : {Pa.Hop.inside(_, g, n, a, at, total) == Pa.Hop{g, head, Nat.add(total, U32.to_nat(cost)), True{}} : Pa.Hop}
  %ed : {Pa.Hop.head(_, n, a, total) == Pa.Hop{g, head, Nat.add(total, U32.to_nat(cost)), True{}} : Pa.Hop}
  %ec : {Pa.Hop.cost(_, head, total) == Pa.Hop{g, head, Nat.add(total, U32.to_nat(cost)), True{}} : Pa.Hop}
  {==}

law hop.no:
  for -g: Array<U32>
  for +n: U32
  for +a: U32
  for +at: U32
  for +total: Nat
  for +lo: U32
  for +hi: U32
  for +el: {(g, lo) == Array.get(U32, g, (at + 2 : U32)) : Array<U32> & U32}
  for +eh: {(g, hi) == Array.get(U32, g, (at + 3 : U32)) : Array<U32> & U32}
  for +ok: {Ok(n, at, lo, a, hi) == False{} : Bool}
  {Pa.Hop.go(True{}, g, n, a, at, total) == Pa.Hop{g, at, total, False{}} : Pa.Hop}

def hop.no(g, n, a, at, total, lo, hi, el, eh, ok):
  %el : {Pa.Hop.lo(_, n, a, at, total) == Pa.Hop{g, at, total, False{}} : Pa.Hop}
  %eh : {Pa.Hop.hi(_, lo, n, a, at, total) == Pa.Hop{g, at, total, False{}} : Pa.Hop}
  %Equal.sym(Bool, Ok(n, at, lo, a, hi), False{}, ok) : {Pa.Hop.inside(_, g, n, a, at, total) == Pa.Hop{g, at, total, False{}} : Pa.Hop}
  {==}

law ends.no:
  for -g: Array<U32>
  for +t: List<&2, U32>
  for +n: U32
  for +a: U32
  for +at: U32
  for +dst: U32
  for +total: Nat
  for +c: Nat
  for +hop: {Pa.Hop.go(True{}, g, n, a, at, total) == Pa.Hop{g, at, total, False{}} : Pa.Hop}
  for +e: Ends(a <> t, g, n, at, dst, total, c)
  {None{} == Some{c} : Maybe<&2, Nat>}

def ends.no(g, t, n, a, at, dst, total, c, hop, e):
  %walk.false(t, g, n, at, total) : {Pa.Walked.cost(Pa.Path.end(_, dst)) == Some{c} : Maybe<&2, Nat>}
  %hop : {Pa.Walked.cost(Pa.Path.end(Pa.Path.walk(t, _, n), dst)) == Some{c} : Maybe<&2, Nat>}
  e

law ends.yes:
  for -g: Array<U32>
  for -h: Pa.Hop
  for +t: List<&2, U32>
  for +n: U32
  for +a: U32
  for +at: U32
  for +dst: U32
  for +total: Nat
  for +c: Nat
  for +hop: {Pa.Hop.go(True{}, g, n, a, at, total) == h : Pa.Hop}
  for +e: Ends(a <> t, g, n, at, dst, total, c)
  {Pa.Walked.cost(Pa.Path.end(Pa.Path.walk(t, h, n), dst)) == Some{c} : Maybe<&2, Nat>}

def ends.yes(g, h, t, n, a, at, dst, total, c, hop, e):
  %hop : {Pa.Walked.cost(Pa.Path.end(Pa.Path.walk(t, _, n), dst)) == Some{c} : Maybe<&2, Nat>}
  e

# What a recursive call proves: the rest of the path, from any live copy.
def Rest(+t: List<&2, U32>, +n: U32, +dst: U32, +c: Nat) -> Type:
  @h: Array<U32> -> @head: U32 -> @total: Nat -> Ends(t, h, n, head, dst, total, c) -> Sp.Walks(t, h, n, head, dst, total, c)

law leaves.yes:
  for -g: Array<U32>
  for +n: U32
  for +a: U32
  for +at: U32
  for +lo: U32
  for +hi: U32
  for +el: {(g, lo) == Array.get(U32, g, (at + 2 : U32)) : Array<U32> & U32}
  for +eh: {(g, hi) == Array.get(U32, g, (at + 3 : U32)) : Array<U32> & U32}
  for +ok: {Ok(n, at, lo, a, hi) == True{} : Bool}
  Sp.Leaves(g, n, at, a)

def leaves.yes(g, n, a, at, lo, hi, el, eh, ok):
  %at.is(g, (at + 2 : U32), lo, el) : {U32.is_lt(at, n) && U32.is_le(_, a) && U32.is_lt(a, Sp.At(g, (at + 3 : U32))) == True{} : Bool}
  %at.is(g, (at + 3 : U32), hi, eh) : {U32.is_lt(at, n) && U32.is_le(lo, a) && U32.is_lt(a, _) == True{} : Bool}
  ok

law walks.on:
  for -g: Array<U32>
  for -h: Array<U32>
  for +t: List<&2, U32>
  for +n: U32
  for +a: U32
  for +dst: U32
  for +total: Nat
  for +c: Nat
  for +head: U32
  for +cost: U32
  for +ed: {(g, head) == Array.get(U32, g, (n + (2 * a : U32) + 4 : U32)) : Array<U32> & U32}
  for +ec: {(g, cost) == Array.get(U32, g, (n + (2 * a : U32) + 5 : U32)) : Array<U32> & U32}
  for +eh: {h == g : Array<U32>}
  for w: Sp.Walks(t, h, n, head, dst, Nat.add(total, U32.to_nat(cost)), c)
  Sp.Walks(t, g, n, Sp.Head(g, n, a), dst, Nat.add(total, Sp.Cost(g, n, a)), c)

def walks.on(g, h, t, n, a, dst, total, c, head, cost, ed, ec, eh, w):
  %at.is(g, (n + (2 * a : U32) + 4 : U32), head, ed) : Sp.Walks(t, g, n, _, dst, Nat.add(total, Sp.Cost(g, n, a)), c)
  %at.is(g, (n + (2 * a : U32) + 5 : U32), cost, ec) : Sp.Walks(t, g, n, head, dst, Nat.add(total, U32.to_nat(_)), c)
  %eh : Sp.Walks(t, _, n, head, dst, Nat.add(total, U32.to_nat(cost)), c)
  w

law ends.on:
  for -g: Array<U32>
  for -h: Array<U32>
  for +t: List<&2, U32>
  for +n: U32
  for +head: U32
  for +dst: U32
  for +total: Nat
  for +c: Nat
  for +eh: {h == g : Array<U32>}
  for +e: Ends(t, g, n, head, dst, total, c)
  Ends(t, h, n, head, dst, total, c)

def ends.on(g, h, t, n, head, dst, total, c, eh, e):
  %Equal.sym(Array<U32>, h, g, eh) : Ends(t, _, n, head, dst, total, c)
  e

def walk.yes(-g: Array<U32>, h: Array<U32>, +t: List<&2, U32>, +n: U32, +a: U32, +at: U32, +dst: U32, +total: Nat, +c: Nat, +lo: U32, +hi: U32, +head: U32, +cost: U32, +el: {(g, lo) == Array.get(U32, g, (at + 2 : U32)) : Array<U32> & U32}, +eh: {(g, hi) == Array.get(U32, g, (at + 3 : U32)) : Array<U32> & U32}, +ed: {(g, head) == Array.get(U32, g, (n + (2 * a : U32) + 4 : U32)) : Array<U32> & U32}, +ec: {(g, cost) == Array.get(U32, g, (n + (2 * a : U32) + 5 : U32)) : Array<U32> & U32}, +es: {h == g : Array<U32>}, +e: Ends(a <> t, g, n, at, dst, total, c), rest: Rest(t, n, dst, c), +ok: {Ok(n, at, lo, a, hi) == True{} : Bool}) -> Sp.Walks(a <> t, g, n, at, dst, total, c):
  +sum = Nat.add(total, U32.to_nat(cost))
  +hop = hop.yes(g, n, a, at, total, lo, hi, head, cost, el, eh, ed, ec, ok)
  +next = ends.yes(g, Pa.Hop{g, head, sum, True{}}, t, n, a, at, dst, total, c, hop, e)
  (leaves.yes(g, n, a, at, lo, hi, el, eh, ok), walks.on(g, h, t, n, a, dst, total, c, head, cost, ed, ec, es, rest(h, head, sum, ends.on(g, h, t, n, head, dst, sum, c, es, next))))

def walk.no(-g: Array<U32>, +t: List<&2, U32>, +n: U32, +a: U32, +at: U32, +dst: U32, +total: Nat, +c: Nat, +lo: U32, +hi: U32, +el: {(g, lo) == Array.get(U32, g, (at + 2 : U32)) : Array<U32> & U32}, +eh: {(g, hi) == Array.get(U32, g, (at + 3 : U32)) : Array<U32> & U32}, +e: Ends(a <> t, g, n, at, dst, total, c), +ok: {Ok(n, at, lo, a, hi) == False{} : Bool}) -> Sp.Walks(a <> t, g, n, at, dst, total, c):
  none.some(c, Sp.Walks(a <> t, g, n, at, dst, total, c), ends.no(g, t, n, a, at, dst, total, c, hop.no(g, n, a, at, total, lo, hi, el, eh, ok), e))

def walk.go(-g: Array<U32>, h: Array<U32>, +t: List<&2, U32>, +n: U32, +a: U32, +at: U32, +dst: U32, +total: Nat, +c: Nat, +lo: U32, +hi: U32, +head: U32, +cost: U32, +el: {(g, lo) == Array.get(U32, g, (at + 2 : U32)) : Array<U32> & U32}, +eh: {(g, hi) == Array.get(U32, g, (at + 3 : U32)) : Array<U32> & U32}, +ed: {(g, head) == Array.get(U32, g, (n + (2 * a : U32) + 4 : U32)) : Array<U32> & U32}, +ec: {(g, cost) == Array.get(U32, g, (n + (2 * a : U32) + 5 : U32)) : Array<U32> & U32}, +es: {h == g : Array<U32>}, +e: Ends(a <> t, g, n, at, dst, total, c), rest: Rest(t, n, dst, c)) -> Sp.Walks(a <> t, g, n, at, dst, total, c):
  L.cases(Ok(n, at, lo, a, hi), Sp.Walks(a <> t, g, n, at, dst, total, c), ok => walk.yes(g, h, t, n, a, at, dst, total, c, lo, hi, head, cost, el, eh, ed, ec, es, e, rest, ok), ok => walk.no(g, t, n, a, at, dst, total, c, lo, hi, el, eh, e, ok))

def walk.cons(-g: Array<U32>, +t: List<&2, U32>, +n: U32, +a: U32, +at: U32, +dst: U32, +total: Nat, +c: Nat, +e: Ends(a <> t, g, n, at, dst, total, c), rest: Rest(t, n, dst, c), f: Reads(Arc.ids(n, a, at), g)) -> Sp.Walks(a <> t, g, n, at, dst, total, c):
  (lo, el, hi, eh, head, ed, cost, ec, h, es) = f
  walk.go(g, h, t, n, a, at, dst, total, c, lo, hi, head, cost, el, eh, ed, ec, es, e, rest)

# A path that costs c from `at` walks the graph from `at`.
def walk.sound(xs: List<&2, U32>, g: Array<U32>, +n: U32, +at: U32, +dst: U32, +total: Nat, +c: Nat, +e: Ends(xs, g, n, at, dst, total, c)) -> Sp.Walks(xs, g, n, at, dst, total, c):
  match xs:
    case Nil{}:
      end.sound(U32.is_eq(at, dst), g, total, c, e)
    case +a <> +t:
      walk.cons(g, t, n, a, at, dst, total, c, e, h => head => sum => ev => walk.sound(t, h, n, head, dst, sum, c, ev), reads(Arc.ids(n, a, at), g))

# Reported times
# --------------

# What a reported time promises: the cell's own path walks the graph at that cost.
def Told(-x: Pa.Cell, -g: Array<U32>, +n: U32, +limit: U32, +src: U32, +dst: U32, +c: Nat) -> Type:
  Sp.Walks(Pa.Cell.path(x), g, n, src, dst, 0n, c) & {Nat.is_le(c, U32.to_nat(limit)) == True{} : Bool}

# Three facts about a cell, read off how it was judged.
def Judged(-x: Pa.Cell, -m: Maybe<&2, Nat>, +path: List<&2, U32>, +limit: Nat, +c: Nat) -> Type:
  {m == Some{c} : Maybe<&2, Nat>} & {path == Pa.Cell.path(x) : List<&2, U32>} & {Nat.is_le(c, limit) == True{} : Bool}

law cell.limit:
  for +t: Nat
  for +limit: Nat
  for +c: Nat
  for +tc: {t == c : Nat}
  for +less: {Nat.is_le(t, limit) == True{} : Bool}
  {Nat.is_le(c, limit) == True{} : Bool}

def cell.limit(t, limit, c, tc, less):
  %tc : {Nat.is_le(_, limit) == True{} : Bool}
  less

law cell.some:
  for +t: Nat
  for +c: Nat
  for +tc: {t == c : Nat}
  {Some{t} == Some{c} : Maybe<&2, Nat>}

def cell.some(t, c, tc):
  %tc : {Some{t} == Some{_} : Maybe<&2, Nat>}
  {==}

def Agreed(+l: Bool, -x: Pa.Cell, +path: List<&2, U32>, +t: Nat, +c: Nat) -> Type:
  {l == True{} : Bool} & {t == c : Nat} & {path == Pa.Cell.path(x) : List<&2, U32>}

def cell.agree(+f: Bool, +l: Bool, -g: Array<U32>, -w: Array<U32>, +path: List<&2, U32>, +t: Nat, +c: Nat, +e: {Pa.Cell.cost(Pa.Cell.agree(Bool.and(f, l), g, w, path, t)) == Some{c} : Maybe<&2, Nat>}) -> Agreed(l, Pa.Cell.agree(Bool.and(f, l), g, w, path, t), path, t, c):
  match f l:
    case True{} True{}:
      ({==}, some.inj(t, c, e), {==})
    case True{} False{}:
      none.some(c, Agreed(False{}, Pa.Cell{g, w, Nil{}, None{}, True{}}, path, t, c), e)
    case False{} _:
      none.some(c, Agreed(l, Pa.Cell{g, w, Nil{}, None{}, True{}}, path, t, c), e)

def cell.judged.go(-x: Pa.Cell, +path: List<&2, U32>, +t: Nat, +limit: Nat, +c: Nat, +less: {Nat.is_le(t, limit) == True{} : Bool}, +tc: {t == c : Nat}, +ep: {path == Pa.Cell.path(x) : List<&2, U32>}) -> Judged(x, Some{t}, path, limit, c):
  (cell.some(t, c, tc), ep, cell.limit(t, limit, c, tc, less))

def cell.judged(-x: Pa.Cell, +path: List<&2, U32>, +t: Nat, +limit: Nat, +c: Nat, r: Agreed(Nat.is_le(t, limit), x, path, t, c)) -> Judged(x, Some{t}, path, limit, c):
  (less, tc, ep) = r
  cell.judged.go(x, path, t, limit, c, less, tc, ep)

def cell.judge(+m: Maybe<&2, Nat>, -g: Array<U32>, -w: Array<U32>, +path: List<&2, U32>, +d: Nat, +limit: Nat, +c: Nat, +e: {Pa.Cell.cost(Pa.Cell.judge(m, g, w, path, d, limit)) == Some{c} : Maybe<&2, Nat>}) -> Judged(Pa.Cell.judge(m, g, w, path, d, limit), m, path, limit, c):
  match m:
    case None{}:
      none.some(c, Judged(Pa.Cell{g, w, Nil{}, None{}, True{}}, None{}, path, limit, c), e)
    case Some{+t}:
      cell.judged(Pa.Cell.judge(Some{t}, g, w, path, d, limit), path, t, limit, c, cell.agree(Nat.is_eq(t, d), Nat.is_le(t, limit), g, w, path, t, c, e))

def cell.end(x: Pa.Walked, -w: Array<U32>, +path: List<&2, U32>, +d: Nat, +limit: Nat, +c: Nat, +e: {Pa.Cell.cost(Pa.Cell.end(x, w, path, d, limit)) == Some{c} : Maybe<&2, Nat>}) -> Judged(Pa.Cell.end(x, w, path, d, limit), Pa.Walked.cost(x), path, limit, c):
  match x:
    case Pa.Walked{g, +m}:
      cell.judge(m, g, w, path, d, limit, c, e)

law cell.on:
  for -g: Array<U32>
  for -h: Array<U32>
  for -w: Array<U32>
  for +n: U32
  for +src: U32
  for +dst: U32
  for +path: List<&2, U32>
  for +d: Nat
  for +limit: Nat
  for +c: Nat
  for +eh: {h == g : Array<U32>}
  for +e: {Pa.Cell.cost(Pa.Cell.end(Pa.Path.check(g, n, src, dst, path), w, path, d, limit)) == Some{c} : Maybe<&2, Nat>}
  {Pa.Cell.cost(Pa.Cell.end(Pa.Path.check(h, n, src, dst, path), w, path, d, limit)) == Some{c} : Maybe<&2, Nat>}

def cell.on(g, h, w, n, src, dst, path, d, limit, c, eh, e):
  %Equal.sym(Array<U32>, h, g, eh) : {Pa.Cell.cost(Pa.Cell.end(Pa.Path.check(_, n, src, dst, path), w, path, d, limit)) == Some{c} : Maybe<&2, Nat>}
  e

law cell.ends:
  for -h: Array<U32>
  for -k: Array<U32>
  for +n: U32
  for +src: U32
  for +dst: U32
  for +path: List<&2, U32>
  for +c: Nat
  for +ek: {k == h : Array<U32>}
  for +e: {Pa.Walked.cost(Pa.Path.check(h, n, src, dst, path)) == Some{c} : Maybe<&2, Nat>}
  Ends(path, k, n, src, dst, 0n, c)

def cell.ends(h, k, n, src, dst, path, c, ek, e):
  %Equal.sym(Array<U32>, k, h, ek) : Ends(path, _, n, src, dst, 0n, c)
  e

law cell.walks:
  for -g: Array<U32>
  for -h: Array<U32>
  for -k: Array<U32>
  for -w: Array<U32>
  for +n: U32
  for +src: U32
  for +dst: U32
  for +path: List<&2, U32>
  for +d: Nat
  for +limit: Nat
  for +c: Nat
  for +eh: {h == g : Array<U32>}
  for +ek: {k == g : Array<U32>}
  for +ep: {path == Pa.Cell.path(Pa.Cell.end(Pa.Path.check(h, n, src, dst, path), w, path, d, limit)) : List<&2, U32>}
  for r: Sp.Walks(path, k, n, src, dst, 0n, c)
  Sp.Walks(Pa.Cell.path(Pa.Cell.end(Pa.Path.check(g, n, src, dst, path), w, path, d, limit)), g, n, src, dst, 0n, c)

def cell.walks(g, h, k, w, n, src, dst, path, d, limit, c, eh, ek, ep, r):
  %eh : Sp.Walks(Pa.Cell.path(Pa.Cell.end(Pa.Path.check(_, n, src, dst, path), w, path, d, limit)), g, n, src, dst, 0n, c)
  %ep : Sp.Walks(_, g, n, src, dst, 0n, c)
  %ek : Sp.Walks(path, _, n, src, dst, 0n, c)
  r

def cell.split(-g: Array<U32>, -h: Array<U32>, k: Array<U32>, -w: Array<U32>, +n: U32, +src: U32, +dst: U32, +path: List<&2, U32>, +d: Nat, +limit: U32, +c: Nat, +eh: {h == g : Array<U32>}, +ek: {k == g : Array<U32>}, j: Judged(Pa.Cell.end(Pa.Path.check(h, n, src, dst, path), w, path, d, U32.to_nat(limit)), Pa.Walked.cost(Pa.Path.check(h, n, src, dst, path)), path, U32.to_nat(limit), c)) -> Told(Pa.Cell.end(Pa.Path.check(g, n, src, dst, path), w, path, d, U32.to_nat(limit)), g, n, limit, src, dst, c):
  (ec, ep, less) = j
  +ekh = Equal.trans(Array<U32>, k, g, h, ek, Equal.sym(Array<U32>, h, g, eh))
  (cell.walks(g, h, k, w, n, src, dst, path, d, U32.to_nat(limit), c, eh, ek, ep, walk.sound(path, k, n, src, dst, 0n, c, cell.ends(h, k, n, src, dst, path, c, ekh, ec))), less)

def cell.copied(-g: Array<U32>, h: Array<U32>, k: Array<U32>, -w: Array<U32>, +n: U32, +src: U32, +dst: U32, +path: List<&2, U32>, +d: Nat, +limit: U32, +c: Nat, +e: {Pa.Cell.cost(Pa.Cell.end(Pa.Path.check(g, n, src, dst, path), w, path, d, U32.to_nat(limit))) == Some{c} : Maybe<&2, Nat>}, +eh: {h == g : Array<U32>}, +ek: {k == g : Array<U32>}) -> Told(Pa.Cell.end(Pa.Path.check(g, n, src, dst, path), w, path, d, U32.to_nat(limit)), g, n, limit, src, dst, c):
  cell.split(g, h, k, w, n, src, dst, path, d, limit, c, eh, ek, cell.end(Pa.Path.check(h, n, src, dst, path), w, path, d, U32.to_nat(limit), c, cell.on(g, h, w, n, src, dst, path, d, U32.to_nat(limit), c, eh, e)))

def cell.copies(-g: Array<U32>, -w: Array<U32>, +n: U32, +src: U32, +dst: U32, +path: List<&2, U32>, +d: Nat, +limit: U32, +c: Nat, +e: {Pa.Cell.cost(Pa.Cell.end(Pa.Path.check(g, n, src, dst, path), w, path, d, U32.to_nat(limit))) == Some{c} : Maybe<&2, Nat>}, l: Copies(g)) -> Told(Pa.Cell.end(Pa.Path.check(g, n, src, dst, path), w, path, d, U32.to_nat(limit)), g, n, limit, src, dst, c):
  (h, k, eh, ek) = l
  cell.copied(g, h, k, w, n, src, dst, path, d, limit, c, e, eh, ek)

def cell.walk(b: Pa.Back, g: Array<U32>, +n: U32, +src: U32, +dst: U32, +d: U32, +limit: U32, +c: Nat, +e: {Pa.Cell.cost(Pa.Cell.walk(b, g, n, src, dst, d, limit)) == Some{c} : Maybe<&2, Nat>}) -> Told(Pa.Cell.walk(b, g, n, src, dst, d, limit), g, n, limit, src, dst, c):
  match b:
    case Pa.Back{w, +path}:
      cell.copies(g, w, n, src, dst, path, U32.to_nat(d), limit, c, e, copy(g))

def cell.dist(p: Array<U32> & U32, g: Array<U32>, +fuel: Nat, +n: U32, +limit: U32, +src: U32, +dst: U32, +c: Nat, +e: {Pa.Cell.cost(Pa.Cell.dist(p, g, fuel, n, limit, src, dst)) == Some{c} : Maybe<&2, Nat>}) -> Told(Pa.Cell.dist(p, g, fuel, n, limit, src, dst), g, n, limit, src, dst, c):
  match p:
    case (w, +d):
      cell.walk(Pa.Back.read(U32.is_eq(src, dst), fuel, n, src, dst, w), g, n, src, dst, d, limit, c, e)

def cell.seen(b: Bool, g: Array<U32>, w: Array<U32>, +fuel: Nat, +n: U32, +limit: U32, +src: U32, +dst: U32, +c: Nat, +e: {Pa.Cell.cost(Pa.Cell.seen(b, g, w, fuel, n, limit, src, dst)) == Some{c} : Maybe<&2, Nat>}) -> Told(Pa.Cell.seen(b, g, w, fuel, n, limit, src, dst), g, n, limit, src, dst, c):
  match b:
    case True{}:
      cell.dist(Array.get(U32, w, dst), g, fuel, n, limit, src, dst, c, e)
    case False{}:
      none.some(c, Told(Pa.Cell{g, w, Nil{}, None{}, False{}}, g, n, limit, src, dst, c), e)

def cell.stamp(p: Array<U32> & U32, g: Array<U32>, +fuel: Nat, +n: U32, +limit: U32, +src: U32, +dst: U32, +stamp: U32, +c: Nat, +e: {Pa.Cell.cost(Pa.Cell.stamp(p, g, fuel, n, limit, src, dst, stamp)) == Some{c} : Maybe<&2, Nat>}) -> Told(Pa.Cell.stamp(p, g, fuel, n, limit, src, dst, stamp), g, n, limit, src, dst, c):
  match p:
    case (w, +s):
      cell.seen(U32.is_eq(s, stamp), g, w, fuel, n, limit, src, dst, c, e)

# Any time a lookup reports is a real path's cost, within the limit.
def told(g: Array<U32>, w: Array<U32>, +fuel: Nat, +n: U32, +limit: U32, +src: U32, +dst: U32, +stamp: U32, +c: Nat, +e: {Pa.Cell.cost(Pa.Cell.read(g, w, fuel, n, limit, src, dst, stamp)) == Some{c} : Maybe<&2, Nat>}) -> Told(Pa.Cell.read(g, w, fuel, n, limit, src, dst, stamp), g, n, limit, src, dst, c):
  cell.stamp(Array.get(U32, w, (n + dst : U32)), g, fuel, n, limit, src, dst, stamp, c, e)

# The search keeps the graph
# --------------------------

law keep.next:
  for -g: Array<U32>
  for -h: Array<U32>
  for -t: Array<U32>
  for +et: {t == g : Array<U32>}
  for +eh: {h == g : Array<U32>}
  {t == h : Array<U32>}

def keep.next(g, h, t, et, eh):
  Equal.trans(Array<U32>, t, g, h, et, Equal.sym(Array<U32>, h, g, eh))

def keep.pair(-g: Array<U32>, +i: U32, -P: (Array<U32> & U32) -> Type, rest: (@h: Array<U32> -> @v: U32 -> {h == g : Array<U32>} -> P((h, v))), +v: U32, +ev: {(g, v) == Array.get(U32, g, i) : Array<U32> & U32}, h: Array<U32>, +eh: {h == g : Array<U32>}) -> P(Array.get(U32, g, i)):
  %ev : P(_)
  %eh : P((_, v))
  rest(h, v, eh)

def keep.split(-g: Array<U32>, +i: U32, -P: (Array<U32> & U32) -> Type, rest: (@h: Array<U32> -> @v: U32 -> {h == g : Array<U32>} -> P((h, v))), f: Reads([i], g)) -> P(Array.get(U32, g, i)):
  (v, ev, h, eh) = f
  keep.pair(g, i, P, rest, v, ev, h, eh)

# Reading a word and carrying on with a live copy proves the same as reading it.
def keep.via(g: Array<U32>, +i: U32, -P: (Array<U32> & U32) -> Type, rest: (@h: Array<U32> -> @v: U32 -> {h == g : Array<U32>} -> P((h, v)))) -> P(Array.get(U32, g, i)):
  keep.split(g, i, P, rest, reads([i], g))

def keep.out(gp: Array<U32> & U32, wp: Array<U32> & U32, +settled: U32, +why: S.Why, -t: Array<U32>, +et: {t == Sp.Fst(gp) : Array<U32>}) -> {t == S.Out.graph(S.Out.make(gp, wp, settled, why)) : Array<U32>}:
  match gp:
    case (g, _):
      match wp:
        case (w, _):
          et

# Generated from Search.go's arms, which it mirrors one for one: it reads the
# graph where the search reads it and passes everything else along.
def keep(f: Nat, m: S.Mode, b: Bool, +hf: Nat, +n: U32, +h: U32, +cap: U32, +limit: U32, +stamp: U32, +size: U32, +settled: U32, +key: U32, +node: U32, +a: U32, +e: U32, +x: U32, +y: U32, gp: Array<U32> & U32, wp: Array<U32> & U32, -t: Array<U32>, +et: {t == Sp.Fst(gp) : Array<U32>}) -> {t == S.Out.graph(S.Search.go(f, m, b, hf, n, h, cap, limit, stamp, size, settled, key, node, a, e, x, y, gp, wp)) : Array<U32>}:
  match f:
    case 0n:
      keep.out(gp, wp, settled, S.OutOfFuel{}, t, et)
    case 1n+k:
      match m:
        case S.AtNext{}:
          keep(k, S.AtRoot{}, U32.is_zero(size), hf, n, h, cap, limit, stamp, size, settled, key, node, a, e, x, y, gp, wp, t, et)
        case S.AtRoot{}:
          match b:
            case True{}:
              keep.out(gp, wp, settled, S.Finished{}, t, et)
            case False{}:
              match wp:
                case (w, _):
                  keep(k, S.AtKey{}, False{}, hf, n, h, cap, limit, stamp, size, settled, key, node, a, e, x, y, gp, Array.get(U32, w, (h + 2 : U32)), t, et)
        case S.AtKey{}:
          match wp:
            case (w, +v):
              keep(k, S.AtNode{}, False{}, hf, n, h, cap, limit, stamp, size, settled, v, node, a, e, x, y, gp, Array.get(U32, w, (h + 3 : U32)), t, et)
        case S.AtNode{}:
          match wp:
            case (w, +v):
              keep(k, S.AtLast{}, False{}, hf, n, h, cap, limit, stamp, size, settled, key, v, a, e, x, y, gp, Array.get(U32, w, (h + (2 * size : U32) : U32)), t, et)
        case S.AtLast{}:
          match wp:
            case (w, +v):
              keep(k, S.AtSift{}, False{}, hf, n, h, cap, limit, stamp, size, settled, key, node, a, e, v, y, gp, Array.get(U32, w, (h + (2 * size : U32) + 1 : U32)), t, et)
        case S.AtSift{}:
          match wp:
            case (w, +v):
              +left = (size - 1 : U32)
              keep(k, S.AtDist{}, False{}, hf, n, h, cap, limit, stamp, left, settled, key, node, a, e, x, y, gp, Array.get(U32, S.Heap.sink(hf, S.SinkLook{}, False{}, h, left, 1, x, v, 0, 0, (w, 0)), node), t, et)
        case S.AtDist{}:
          match wp:
            case (w, +d):
              keep(k, S.AtFresh{}, U32.is_eq(d, key), hf, n, h, cap, limit, stamp, size, settled, key, node, a, e, x, y, gp, (w, 0), t, et)
        case S.AtFresh{}:
          match b:
            case True{}:
              match gp:
                case (g, _):
                  keep.via(g, (node + 2 : U32), q => {t == S.Out.graph(S.Search.go(k, S.AtFirst{}, False{}, hf, n, h, cap, limit, stamp, size, (settled + 1 : U32), key, node, a, e, x, y, q, wp)) : Array<U32>}, r => u => eh => keep(k, S.AtFirst{}, False{}, hf, n, h, cap, limit, stamp, size, (settled + 1 : U32), key, node, a, e, x, y, (r, u), wp, t, keep.next(g, r, t, et, eh)))
            case False{}:
              keep(k, S.AtNext{}, False{}, hf, n, h, cap, limit, stamp, size, settled, key, node, a, e, x, y, gp, wp, t, et)
        case S.AtFirst{}:
          match gp:
            case (g, +v):
              keep.via(g, (node + 3 : U32), q => {t == S.Out.graph(S.Search.go(k, S.AtEnd{}, False{}, hf, n, h, cap, limit, stamp, size, settled, key, node, v, e, x, y, q, wp)) : Array<U32>}, r => u => eh => keep(k, S.AtEnd{}, False{}, hf, n, h, cap, limit, stamp, size, settled, key, node, v, e, x, y, (r, u), wp, t, keep.next(g, r, t, et, eh)))
        case S.AtEnd{}:
          match gp:
            case (g, +v):
              keep(k, S.AtArc{}, U32.is_lt(a, v), hf, n, h, cap, limit, stamp, size, settled, key, node, a, v, x, y, (g, 0), wp, t, et)
        case S.AtArc{}:
          match b:
            case True{}:
              match gp:
                case (g, _):
                  keep.via(g, (n + (2 * a : U32) + 4 : U32), q => {t == S.Out.graph(S.Search.go(k, S.AtHead{}, False{}, hf, n, h, cap, limit, stamp, size, settled, key, node, a, e, x, y, q, wp)) : Array<U32>}, r => u => eh => keep(k, S.AtHead{}, False{}, hf, n, h, cap, limit, stamp, size, settled, key, node, a, e, x, y, (r, u), wp, t, keep.next(g, r, t, et, eh)))
            case False{}:
              keep(k, S.AtNext{}, False{}, hf, n, h, cap, limit, stamp, size, settled, key, node, a, e, x, y, gp, wp, t, et)
        case S.AtHead{}:
          match gp:
            case (g, +v):
              keep.via(g, (n + (2 * a : U32) + 5 : U32), q => {t == S.Out.graph(S.Search.go(k, S.AtCost{}, False{}, hf, n, h, cap, limit, stamp, size, settled, key, node, a, e, v, y, q, wp)) : Array<U32>}, r => u => eh => keep(k, S.AtCost{}, False{}, hf, n, h, cap, limit, stamp, size, settled, key, node, a, e, v, y, (r, u), wp, t, keep.next(g, r, t, et, eh)))
        case S.AtCost{}:
          match gp:
            case (g, +v):
              +nd = (key + v : U32)
              keep(k, S.AtNear{}, U32.is_le(nd, limit), hf, n, h, cap, limit, stamp, size, settled, key, node, a, e, x, nd, (g, 0), wp, t, et)
        case S.AtNear{}:
          match b:
            case True{}:
              match wp:
                case (w, _):
                  keep(k, S.AtBack{}, False{}, hf, n, h, cap, limit, stamp, size, settled, key, node, a, e, x, y, gp, S.Relax.run(w, hf, n, h, cap, size, stamp, a, node, x, y), t, et)
            case False{}:
              +c = (a + 1 : U32)
              keep(k, S.AtArc{}, U32.is_lt(c, e), hf, n, h, cap, limit, stamp, size, settled, key, node, c, e, x, y, gp, wp, t, et)
        case S.AtBack{}:
          match wp:
            case (w, +s):
              keep(k, S.AtRoom{}, U32.is_eq(s, S.Full()), hf, n, h, cap, limit, stamp, s, settled, key, node, a, e, x, y, gp, (w, 0), t, et)
        case S.AtRoom{}:
          match b:
            case True{}:
              keep.out(gp, wp, settled, S.HeapFull{}, t, et)
            case False{}:
              +c = (a + 1 : U32)
              keep(k, S.AtArc{}, U32.is_lt(c, e), hf, n, h, cap, limit, stamp, size, settled, key, node, c, e, x, y, gp, wp, t, et)

# A search hands back the graph it was given.
def keeps(+fuel: Nat, +hf: Nat, g: Array<U32>, w: Array<U32>, +n: U32, +cap: U32, +limit: U32, +src: U32, +stamp: U32) -> {g == S.Out.graph(S.Search.run(fuel, hf, g, w, n, cap, limit, src, stamp)) : Array<U32>}:
  +h = (4 * n : U32)
  w1 = Array.set(U32, Array.set(U32, w, src, 0), (n + src : U32), stamp)
  w2 = S.Heap.put(w1, h, 1, 0, src)
  keep(fuel, S.AtNext{}, False{}, hf, n, h, cap, limit, stamp, 1, 0, 0, 0, 0, 0, 0, 0, (g, 0), (w2, 0), g, {==})

# A lookup keeps the graph too
# ----------------------------

def Hop.graph(h: Pa.Hop) -> Array<U32>:
  match h:
    case Pa.Hop{g, _, _, _}:
      g

def walk.keep.yes(-g: Array<U32>, h: Array<U32>, +t: List<&2, U32>, +n: U32, +a: U32, +at: U32, +total: Nat, +lo: U32, +hi: U32, +head: U32, +cost: U32, +el: {(g, lo) == Array.get(U32, g, (at + 2 : U32)) : Array<U32> & U32}, +eh: {(g, hi) == Array.get(U32, g, (at + 3 : U32)) : Array<U32> & U32}, +ed: {(g, head) == Array.get(U32, g, (n + (2 * a : U32) + 4 : U32)) : Array<U32> & U32}, +ec: {(g, cost) == Array.get(U32, g, (n + (2 * a : U32) + 5 : U32)) : Array<U32> & U32}, +es: {h == g : Array<U32>}, rest: (@r: Array<U32> -> @head2: U32 -> @sum: Nat -> {r == Hop.graph(Pa.Path.walk(t, Pa.Hop{r, head2, sum, True{}}, n)) : Array<U32>}), +ok: {Ok(n, at, lo, a, hi) == True{} : Bool}) -> {g == Hop.graph(Pa.Path.walk(a <> t, Pa.Hop{g, at, total, True{}}, n)) : Array<U32>}:
  +sum = Nat.add(total, U32.to_nat(cost))
  %Equal.sym(Pa.Hop, Pa.Hop.go(True{}, g, n, a, at, total), Pa.Hop{g, head, sum, True{}}, hop.yes(g, n, a, at, total, lo, hi, head, cost, el, eh, ed, ec, ok)) : {g == Hop.graph(Pa.Path.walk(t, _, n)) : Array<U32>}
  %es : {_ == Hop.graph(Pa.Path.walk(t, Pa.Hop{_, head, sum, True{}}, n)) : Array<U32>}
  rest(h, head, sum)

def walk.keep.no(-g: Array<U32>, +t: List<&2, U32>, +n: U32, +a: U32, +at: U32, +total: Nat, +lo: U32, +hi: U32, +el: {(g, lo) == Array.get(U32, g, (at + 2 : U32)) : Array<U32> & U32}, +eh: {(g, hi) == Array.get(U32, g, (at + 3 : U32)) : Array<U32> & U32}, +ok: {Ok(n, at, lo, a, hi) == False{} : Bool}) -> {g == Hop.graph(Pa.Path.walk(a <> t, Pa.Hop{g, at, total, True{}}, n)) : Array<U32>}:
  %Equal.sym(Pa.Hop, Pa.Hop.go(True{}, g, n, a, at, total), Pa.Hop{g, at, total, False{}}, hop.no(g, n, a, at, total, lo, hi, el, eh, ok)) : {g == Hop.graph(Pa.Path.walk(t, _, n)) : Array<U32>}
  %Equal.sym(Pa.Hop, Pa.Path.walk(t, Pa.Hop{g, at, total, False{}}, n), Pa.Hop{g, at, total, False{}}, walk.false(t, g, n, at, total)) : {g == Hop.graph(_) : Array<U32>}
  {==}

def walk.keep.got(-g: Array<U32>, h: Array<U32>, +t: List<&2, U32>, +n: U32, +a: U32, +at: U32, +total: Nat, +lo: U32, +hi: U32, +head: U32, +cost: U32, +el: {(g, lo) == Array.get(U32, g, (at + 2 : U32)) : Array<U32> & U32}, +eh: {(g, hi) == Array.get(U32, g, (at + 3 : U32)) : Array<U32> & U32}, +ed: {(g, head) == Array.get(U32, g, (n + (2 * a : U32) + 4 : U32)) : Array<U32> & U32}, +ec: {(g, cost) == Array.get(U32, g, (n + (2 * a : U32) + 5 : U32)) : Array<U32> & U32}, +es: {h == g : Array<U32>}, rest: (@r: Array<U32> -> @head2: U32 -> @sum: Nat -> {r == Hop.graph(Pa.Path.walk(t, Pa.Hop{r, head2, sum, True{}}, n)) : Array<U32>})) -> {g == Hop.graph(Pa.Path.walk(a <> t, Pa.Hop{g, at, total, True{}}, n)) : Array<U32>}:
  L.cases(Ok(n, at, lo, a, hi), {g == Hop.graph(Pa.Path.walk(a <> t, Pa.Hop{g, at, total, True{}}, n)) : Array<U32>}, ok => walk.keep.yes(g, h, t, n, a, at, total, lo, hi, head, cost, el, eh, ed, ec, es, rest, ok), ok => walk.keep.no(g, t, n, a, at, total, lo, hi, el, eh, ok))

def walk.keep.cons(-g: Array<U32>, +t: List<&2, U32>, +n: U32, +a: U32, +at: U32, +total: Nat, rest: (@r: Array<U32> -> @head2: U32 -> @sum: Nat -> {r == Hop.graph(Pa.Path.walk(t, Pa.Hop{r, head2, sum, True{}}, n)) : Array<U32>}), f: Reads(Arc.ids(n, a, at), g)) -> {g == Hop.graph(Pa.Path.walk(a <> t, Pa.Hop{g, at, total, True{}}, n)) : Array<U32>}:
  (lo, el, hi, eh, head, ed, cost, ec, h, es) = f
  walk.keep.got(g, h, t, n, a, at, total, lo, hi, head, cost, el, eh, ed, ec, es, rest)

def walk.keep(xs: List<&2, U32>, g: Array<U32>, +n: U32, +at: U32, +total: Nat) -> {g == Hop.graph(Pa.Path.walk(xs, Pa.Hop{g, at, total, True{}}, n)) : Array<U32>}:
  match xs:
    case Nil{}:
      {==}
    case +a <> +t:
      walk.keep.cons(g, t, n, a, at, total, r => head => sum => walk.keep(t, r, n, head, sum), reads(Arc.ids(n, a, at), g))

def Walked.graph(x: Pa.Walked) -> Array<U32>:
  match x:
    case Pa.Walked{g, _}:
      g

def end.keep(c: Bool, -g: Array<U32>, +total: Nat) -> {g == Walked.graph(Pa.Path.end.at(c, g, total)) : Array<U32>}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def hop.end.keep(h: Pa.Hop, +dst: U32) -> {Hop.graph(h) == Walked.graph(Pa.Path.end(h, dst)) : Array<U32>}:
  match h:
    case Pa.Hop{g, +at, +total, ok}:
      end.keep(ok && U32.is_eq(at, dst), g, total)

law check.swap:
  for -k: Array<U32>
  for h: Array<U32>
  for +n: U32
  for +src: U32
  for +path: List<&2, U32>
  for +ehk: {h == k : Array<U32>}
  {h == Hop.graph(Pa.Path.walk(path, Pa.Hop{k, src, 0n, True{}}, n)) : Array<U32>}

def check.swap(k, h, n, src, path, ehk):
  %ehk : {h == Hop.graph(Pa.Path.walk(path, Pa.Hop{_, src, 0n, True{}}, n)) : Array<U32>}
  walk.keep(path, h, n, src, 0n)

def check.keep.copied(-g: Array<U32>, h: Array<U32>, k: Array<U32>, +n: U32, +src: U32, +dst: U32, +path: List<&2, U32>, +eh: {h == g : Array<U32>}, +ek: {k == g : Array<U32>}) -> {g == Walked.graph(Pa.Path.check(g, n, src, dst, path)) : Array<U32>}:
  +ehk = Equal.trans(Array<U32>, h, g, k, eh, Equal.sym(Array<U32>, k, g, ek))
  %eh : {_ == Walked.graph(Pa.Path.check(g, n, src, dst, path)) : Array<U32>}
  %ek : {h == Walked.graph(Pa.Path.check(_, n, src, dst, path)) : Array<U32>}
  Equal.trans(Array<U32>, h, Hop.graph(Pa.Path.walk(path, Pa.Hop{k, src, 0n, True{}}, n)), Walked.graph(Pa.Path.check(k, n, src, dst, path)), check.swap(k, h, n, src, path, ehk), hop.end.keep(Pa.Path.walk(path, Pa.Hop{k, src, 0n, True{}}, n), dst))

def check.keep.copies(-g: Array<U32>, +n: U32, +src: U32, +dst: U32, +path: List<&2, U32>, l: Copies(g)) -> {g == Walked.graph(Pa.Path.check(g, n, src, dst, path)) : Array<U32>}:
  (h, k, eh, ek) = l
  check.keep.copied(g, h, k, n, src, dst, path, eh, ek)

def check.keep(g: Array<U32>, +n: U32, +src: U32, +dst: U32, +path: List<&2, U32>) -> {g == Walked.graph(Pa.Path.check(g, n, src, dst, path)) : Array<U32>}:
  check.keep.copies(g, n, src, dst, path, copy(g))

def agree.keep(c: Bool, -g: Array<U32>, -w: Array<U32>, +path: List<&2, U32>, +t: Nat) -> {g == Pa.Cell.graph(Pa.Cell.agree(c, g, w, path, t)) : Array<U32>}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def judge.keep(+m: Maybe<&2, Nat>, -g: Array<U32>, -w: Array<U32>, +path: List<&2, U32>, +d: Nat, +limit: Nat) -> {g == Pa.Cell.graph(Pa.Cell.judge(m, g, w, path, d, limit)) : Array<U32>}:
  match m:
    case None{}:
      {==}
    case Some{+t}:
      agree.keep(Nat.is_eq(t, d) && Nat.is_le(t, limit), g, w, path, t)

def end.cell.keep(x: Pa.Walked, -w: Array<U32>, +path: List<&2, U32>, +d: Nat, +limit: Nat) -> {Walked.graph(x) == Pa.Cell.graph(Pa.Cell.end(x, w, path, d, limit)) : Array<U32>}:
  match x:
    case Pa.Walked{g, +m}:
      judge.keep(m, g, w, path, d, limit)

law cell.keep.left:
  for -k: Array<U32>
  for h: Array<U32>
  for +n: U32
  for +src: U32
  for +dst: U32
  for +path: List<&2, U32>
  for +ehk: {h == k : Array<U32>}
  {k == Walked.graph(Pa.Path.check(k, n, src, dst, path)) : Array<U32>}

def cell.keep.left(k, h, n, src, dst, path, ehk):
  %ehk : {_ == Walked.graph(Pa.Path.check(_, n, src, dst, path)) : Array<U32>}
  check.keep(h, n, src, dst, path)

def cell.keep.copied(-g: Array<U32>, h: Array<U32>, k: Array<U32>, -w: Array<U32>, +n: U32, +src: U32, +dst: U32, +path: List<&2, U32>, +d: Nat, +limit: Nat, +eh: {h == g : Array<U32>}, +ek: {k == g : Array<U32>}) -> {g == Pa.Cell.graph(Pa.Cell.end(Pa.Path.check(g, n, src, dst, path), w, path, d, limit)) : Array<U32>}:
  +ehk = Equal.trans(Array<U32>, h, g, k, eh, Equal.sym(Array<U32>, k, g, ek))
  %ek : {_ == Pa.Cell.graph(Pa.Cell.end(Pa.Path.check(_, n, src, dst, path), w, path, d, limit)) : Array<U32>}
  Equal.trans(Array<U32>, k, Walked.graph(Pa.Path.check(k, n, src, dst, path)), Pa.Cell.graph(Pa.Cell.end(Pa.Path.check(k, n, src, dst, path), w, path, d, limit)), cell.keep.left(k, h, n, src, dst, path, ehk), end.cell.keep(Pa.Path.check(k, n, src, dst, path), w, path, d, limit))

def cell.keep.copies(-g: Array<U32>, -w: Array<U32>, +n: U32, +src: U32, +dst: U32, +path: List<&2, U32>, +d: Nat, +limit: Nat, l: Copies(g)) -> {g == Pa.Cell.graph(Pa.Cell.end(Pa.Path.check(g, n, src, dst, path), w, path, d, limit)) : Array<U32>}:
  (h, k, eh, ek) = l
  cell.keep.copied(g, h, k, w, n, src, dst, path, d, limit, eh, ek)

def walk.cell.keep(b: Pa.Back, g: Array<U32>, +n: U32, +src: U32, +dst: U32, +d: U32, +limit: U32) -> {g == Pa.Cell.graph(Pa.Cell.walk(b, g, n, src, dst, d, limit)) : Array<U32>}:
  match b:
    case Pa.Back{w, +path}:
      cell.keep.copies(g, w, n, src, dst, path, U32.to_nat(d), U32.to_nat(limit), copy(g))

def dist.keep(p: Array<U32> & U32, g: Array<U32>, +fuel: Nat, +n: U32, +limit: U32, +src: U32, +dst: U32) -> {g == Pa.Cell.graph(Pa.Cell.dist(p, g, fuel, n, limit, src, dst)) : Array<U32>}:
  match p:
    case (w, +d):
      walk.cell.keep(Pa.Back.read(U32.is_eq(src, dst), fuel, n, src, dst, w), g, n, src, dst, d, limit)

def seen.keep(b: Bool, g: Array<U32>, w: Array<U32>, +fuel: Nat, +n: U32, +limit: U32, +src: U32, +dst: U32) -> {g == Pa.Cell.graph(Pa.Cell.seen(b, g, w, fuel, n, limit, src, dst)) : Array<U32>}:
  match b:
    case True{}:
      dist.keep(Array.get(U32, w, dst), g, fuel, n, limit, src, dst)
    case False{}:
      {==}

def stamp.keep(p: Array<U32> & U32, g: Array<U32>, +fuel: Nat, +n: U32, +limit: U32, +src: U32, +dst: U32, +stamp: U32) -> {g == Pa.Cell.graph(Pa.Cell.stamp(p, g, fuel, n, limit, src, dst, stamp)) : Array<U32>}:
  match p:
    case (w, +s):
      seen.keep(U32.is_eq(s, stamp), g, w, fuel, n, limit, src, dst)

# A lookup hands back the graph it was given.
def lookup.keeps(g: Array<U32>, w: Array<U32>, +fuel: Nat, +n: U32, +limit: U32, +src: U32, +dst: U32, +stamp: U32) -> {g == Pa.Cell.graph(Pa.Cell.read(g, w, fuel, n, limit, src, dst, stamp)) : Array<U32>}:
  stamp.keep(Array.get(U32, w, (n + dst : U32)), g, fuel, n, limit, src, dst, stamp)

# Dealing work out
# ----------------

law merge.nil:
  for +s: List<&2, U32>
  {s == Lanes.Deal.merge(U32, Nil{}, s) : List<&2, U32>}

def merge.nil(s):
  match s:
    case Nil{}:
      {==}
    case +x <> t:
      {==}

law merge.swap:
  for +a: List<&2, U32>
  for +b: List<&2, U32>
  for +h: U32
  {Lanes.Deal.merge(U32, h <> b, a) == h <> Lanes.Deal.merge(U32, a, b) : List<&2, U32>}

def merge.swap(a, b, h):
  match a b:
    case Nil{} Nil{}:
      {==}
    case Nil{} +y <> t:
      {==}
    case +x <> s Nil{}:
      %merge.nil(s) : {h <> x <> _ == h <> x <> s : List<&2, U32>}
      {==}
    case +x <> s +y <> t:
      %merge.swap(s, t, y) : {h <> x <> Lanes.Deal.merge(U32, y <> t, s) == h <> x <> _ : List<&2, U32>}
      {==}

law deal.step:
  for +h: U32
  for p: List<&2, U32> & List<&2, U32>
  {h <> Lanes.Deal.undo(U32, p) == Lanes.Deal.undo(U32, Lanes.Deal.put(U32, h, p)) : List<&2, U32>}

def deal.step(h, p):
  match p:
    case (+a, +b):
      Equal.sym(List<&2, U32>, Lanes.Deal.merge(U32, h <> b, a), h <> Lanes.Deal.merge(U32, a, b), merge.swap(a, b, h))

# Dealing a list out and merging it back gives the same list.
def deal.back(xs: List<&2, U32>) -> {xs == Lanes.Deal.undo(U32, Lanes.Deal.split(U32, xs)) : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case +h <> +t:
      %Equal.sym(List<&2, U32>, t, Lanes.Deal.undo(U32, Lanes.Deal.split(U32, t)), deal.back(t)) : {h <> _ == Lanes.Deal.undo(U32, Lanes.Deal.put(U32, h, Lanes.Deal.split(U32, t))) : List<&2, U32>}
      deal.step(h, Lanes.Deal.split(U32, t))

# Fitting the budget
# ------------------

law room.next:
  for +lanes: Nat
  for +d: Nat
  for +e: {lanes == Nat.pow(2n, d) : Nat}
  {Nat.mul(2n, lanes) == Nat.pow(2n, 1n+d) : Nat}

def room.next(lanes, d, e):
  %e : {Nat.mul(2n, lanes) == Nat.mul(2n, _) : Nat}
  {==}

# Every depth the loop stops on has its lanes within the budget.
def room.fits(k: Nat, fits: Bool, +lanes: Nat, +per: Nat, +budget: Nat, +d: Nat, +e: {lanes == Nat.pow(2n, d) : Nat}, +now: {Nat.is_le(Nat.mul(lanes, per), budget) == True{} : Bool}, +more: {fits == Nat.is_le(Nat.mul(Nat.mul(2n, lanes), per), budget) : Bool}) -> {Nat.is_le(Nat.mul(Nat.pow(2n, Lanes.Lanes.room(k, fits, lanes, per, budget, d)), per), budget) == True{} : Bool}:
  match k:
    case 0n:
      %e : {Nat.is_le(Nat.mul(_, per), budget) == True{} : Bool}
      now
    case 1n+f:
      match fits:
        case True{}:
          +next = Nat.mul(2n, lanes)
          room.fits(f, Nat.is_le(Nat.mul(Nat.mul(2n, next), per), budget), next, per, budget, 1n+d, room.next(lanes, d, e), Equal.sym(Bool, True{}, Nat.is_le(Nat.mul(next, per), budget), more), {==})
        case False{}:
          %e : {Nat.is_le(Nat.mul(_, per), budget) == True{} : Bool}
          now

law budget.one:
  for +per: Nat
  for +budget: Nat
  for +e: {Nat.is_le(per, budget) == True{} : Bool}
  {Nat.is_le(Nat.mul(1n, per), budget) == True{} : Bool}

def budget.one(per, budget, e):
  %Equal.sym(Nat, Nat.add(per, 0n), per, L.add_zero(per)) : {Nat.is_le(_, budget) == True{} : Bool}
  e

# The shell's budget check is sound.
def budget.fits(+k: Nat, +per: Nat, +budget: Nat, +e: {Nat.is_le(per, budget) == True{} : Bool}) -> {Nat.is_le(Nat.mul(Nat.pow(2n, Lanes.Lanes.fit(k, per, budget)), per), budget) == True{} : Bool}:
  room.fits(k, Nat.is_le(Nat.mul(Nat.mul(2n, 1n), per), budget), 1n, per, budget, 0n, {==}, budget.one(per, budget, e), {==})

# The law's two halves, from the one proof.
def walks.of(-x: Pa.Cell, -g: Array<U32>, +n: U32, +limit: U32, +src: U32, +dst: U32, +c: Nat, t: Told(x, g, n, limit, src, dst, c)) -> Sp.Walks(Pa.Cell.path(x), g, n, src, dst, 0n, c):
  (w, _) = t
  w

def limit.of(-x: Pa.Cell, -g: Array<U32>, +n: U32, +limit: U32, +src: U32, +dst: U32, +c: Nat, t: Told(x, g, n, limit, src, dst, c)) -> {Nat.is_le(c, U32.to_nat(limit)) == True{} : Bool}:
  (_, l) = t
  l

def told.walks(g: Array<U32>, w: Array<U32>, +fuel: Nat, +n: U32, +limit: U32, +src: U32, +dst: U32, +stamp: U32, +c: Nat, +e: {Pa.Cell.cost(Pa.Cell.read(g, w, fuel, n, limit, src, dst, stamp)) == Some{c} : Maybe<&2, Nat>}) -> Sp.Walks(Pa.Cell.path(Pa.Cell.read(g, w, fuel, n, limit, src, dst, stamp)), g, n, src, dst, 0n, c):
  walks.of(Pa.Cell.read(g, w, fuel, n, limit, src, dst, stamp), g, n, limit, src, dst, c, told(g, w, fuel, n, limit, src, dst, stamp, c, e))

def told.limit(g: Array<U32>, w: Array<U32>, +fuel: Nat, +n: U32, +limit: U32, +src: U32, +dst: U32, +stamp: U32, +c: Nat, +e: {Pa.Cell.cost(Pa.Cell.read(g, w, fuel, n, limit, src, dst, stamp)) == Some{c} : Maybe<&2, Nat>}) -> {Nat.is_le(c, U32.to_nat(limit)) == True{} : Bool}:
  limit.of(Pa.Cell.read(g, w, fuel, n, limit, src, dst, stamp), g, n, limit, src, dst, c, told(g, w, fuel, n, limit, src, dst, stamp, c, e))

law read.same.at:
  for -a: Array<U32>
  for +i: U32
  for +v: U32
  for +e: {(a, v) == Array.get(U32, a, i) : Array<U32> & U32}
  {(a, Sp.At(a, i)) == Array.get(U32, a, i) : Array<U32> & U32}

def read.same.at(a, i, v, e):
  %e : {(a, Sp.Snd(_)) == _ : Array<U32> & U32}
  {==}

def read.of(-a: Array<U32>, +i: U32, r: Read(a, i)) -> {(a, Sp.At(a, i)) == Array.get(U32, a, i) : Array<U32> & U32}:
  (v, e) = r
  read.same.at(a, i, v, e)

def read.law(a: Array<U32>, +i: U32) -> {(a, Sp.At(a, i)) == Array.get(U32, a, i) : Array<U32> & U32}:
  read.of(a, i, read(a, i))
