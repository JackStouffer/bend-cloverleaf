import Base
import ./types.bend as T

# List operations on appraisals. A plan and an instance hold the same bag of
# appraisals, so everything about "exactly one place" comes down to these.

def count.one(a: T.Appraisal, b: T.Appraisal) -> Nat:
  Bool.pick(Nat, T.Appraisal.is_eq(a, b), 1n, 0n)

def count(+a: T.Appraisal, xs: List<&2, T.Appraisal>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case h <> t:
      Nat.add(count.one(a, h), count(a, t))

# Each id at least lo, rising strictly from there.
def rising(xs: List<&2, T.Appraisal>, lo: Nat) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case +h <> t:
      Bool.and(Nat.is_le(lo, T.Appraisal.id(h)), rising(t, 1n+T.Appraisal.id(h)))

def same(xs: List<&2, T.Appraisal>, ys: List<&2, T.Appraisal>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Nil{} y <> yt:
      False{}
    case x <> xt Nil{}:
      False{}
    case x <> xt y <> yt:
      Bool.and(T.Appraisal.is_eq(x, y), same(xt, yt))

def lazy(c: Bool, a: Unit -> List<&2, T.Appraisal>, b: Unit -> List<&2, T.Appraisal>) ->
  List<&2, T.Appraisal>:
  match c:
    case True{}:
      a(Unit{})
    case False{}:
      b(Unit{})

def le(a: T.Appraisal, b: T.Appraisal) -> Bool:
  Nat.is_le(T.Appraisal.id(a), T.Appraisal.id(b))

def merge(+xs: List<&2, T.Appraisal>, +ys: List<&2, T.Appraisal>) -> List<&2, T.Appraisal>:
  match xs ys:
    case Nil{} _:
      ys
    case x <> xt Nil{}:
      x <> xt
    case x <> xt y <> yt:
      lazy(le(x, y), u => x <> merge(xt, y <> yt), u => y <> merge(x <> xt, yt))

# A Braun tree: each insert swaps the children, so it stays balanced whatever
# order the jobs arrive in, and the recursion is structural with no fuel.
type Tree is Data:
  Tip{}
  Bin{x: T.Appraisal, l: Tree, r: Tree}

def Tree.add(t: Tree, +v: T.Appraisal) -> Tree:
  match t:
    case Tip{}:
      Bin{v, Tip{}, Tip{}}
    case Bin{x, l, r}:
      Bin{x, Tree.add(r, v), l}

def Tree.of(xs: List<&2, T.Appraisal>, t: Tree) -> Tree:
  match xs:
    case Nil{}:
      t
    case h <> r:
      Tree.of(r, Tree.add(t, h))

def Tree.sort(t: Tree) -> List<&2, T.Appraisal>:
  match t:
    case Tip{}:
      Nil{}
    case Bin{x, l, r}:
      a b = Tree.sort(l) Tree.sort(r)
      merge([x], merge(a, b))

def sort(xs: List<&2, T.Appraisal>) -> List<&2, T.Appraisal>:
  Tree.sort(Tree.of(xs, Tip{}))

def without.put(c: Bool, a: T.Appraisal, r: List<&2, T.Appraisal>) -> List<&2, T.Appraisal>:
  match c:
    case True{}:
      r
    case False{}:
      a <> r

# Drops every entry with this id.
def without(xs: List<&2, T.Appraisal>, +i: Nat) -> List<&2, T.Appraisal>:
  match xs:
    case Nil{}:
      Nil{}
    case +h <> t:
      without.put(Nat.is_eq(T.Appraisal.id(h), i), h, without(t, i))

def has_id(xs: List<&2, T.Appraisal>, +i: Nat) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case h <> t:
      Bool.or(Nat.is_eq(T.Appraisal.id(h), i), has_id(t, i))

# Sorted insert into a list sorted by id.
def insert(+xs: List<&2, T.Appraisal>, +j: T.Appraisal) -> List<&2, T.Appraisal>:
  match xs:
    case Nil{}:
      [j]
    case h <> t:
      lazy(Nat.is_le(T.Appraisal.id(j), T.Appraisal.id(h)), u => j <> h <> t, u => h <> insert(t, j))

type Taken is Data:
  Taken{found: Maybe<&2, T.Appraisal>, rest: List<&2, T.Appraisal>}

def Taken.found(t: Taken) -> Maybe<&2, T.Appraisal>:
  match t:
    case Taken{f, r}:
      f

def Taken.rest(t: Taken) -> List<&2, T.Appraisal>:
  match t:
    case Taken{f, r}:
      r

def Taken.cons(h: T.Appraisal, t: Taken) -> Taken:
  match t:
    case Taken{f, r}:
      Taken{f, h <> r}

def take.if(c: Bool, h: T.Appraisal, t: List<&2, T.Appraisal>, rest: Taken) -> Taken:
  match c:
    case True{}:
      Taken{Some{h}, t}
    case False{}:
      Taken.cons(h, rest)

# Takes out the first entry with this id, if there is one.
def take(xs: List<&2, T.Appraisal>, +i: Nat) -> Taken:
  match xs:
    case Nil{}:
      Taken{None{}, Nil{}}
    case +h <> +t:
      take.if(Nat.is_eq(T.Appraisal.id(h), i), h, t, take(t, i))

def has(+a: T.Appraisal, xs: List<&2, T.Appraisal>) -> Bool:
  Nat.is_gt(count(a, xs), 0n)
