import Base
import ../core/types.bend as T
import ../core/times.bend as Tm

# Reading the files the nightly pipeline hands the solver, as pure folds over
# their bytes. scripts/synth.mjs defines instance.bin and road/main.bend defines
# matrix.bin. A matrix is read as it streams in, and only the pairs in reach are
# kept, so a state's full matrix never sits in memory.

def Unreachable() -> Nat:
  4294967295n

def le(+a: U32, +b: U32, +c: U32, +d: U32) -> Nat:
  U32.to_nat(U32.or(a, U32.or(U32.shln(b, 8n), U32.or(U32.shln(c, 16n), U32.shln(d, 24n)))))

# Little-endian words, newest first. Chunks are whole words.
def Words.bytes(xs: List<&2, U32>, acc: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case +a <> +b <> +c <> +d <> t:
      Words.bytes(t, le(a, b, c, d) <> acc)
    case _:
      acc

# instance.bin
# ------------

type Got is Data:
  Got{inst: T.Instance, first: Nat, days: Nat}

def Got.inst(g: Got) -> T.Instance:
  match g:
    case Got{i, f, d}:
      i

def Got.first(g: Got) -> Nat:
  match g:
    case Got{i, f, d}:
      f

def Got.days(g: Got) -> Nat:
  match g:
    case Got{i, f, d}:
      d

type Crews is Data:
  Crews{crews: List<&2, T.Contractor>, rest: List<&2, Nat>}

def Days.put(c: Bool, +d: Nat, rest: List<&2, Nat>) -> List<&2, Nat>:
  match c:
    case True{}:
      d <> rest
    case False{}:
      rest

# Bit k of the mask is day first + k.
def Days.of(n: Nat, +mask: Nat, +day: Nat) -> List<&2, Nat>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      Days.put(Nat.is_eq(Nat.mod(mask, 2n), 1n), day, Days.of(p, Nat.div(mask, 2n), 1n+day))

def Crews.read(n: Nat, xs: List<&2, Nat>, +state: Nat, +span: Nat, +first: Nat, acc: List<&2, T.Contractor>) -> Crews:
  match n:
    case 0n:
      Crews{List.reverse(&2, T.Contractor, acc), xs}
    case 1n+p:
      match xs:
        case id <> lat <> lon <> max <> mask <> +nz <> +t:
          Crews.read(p, List.drop(&2, Nat, t, nz), state, span, first,
            T.Contractor{id, T.Point{lat, lon}, List.take(&2, Nat, t, nz), max, Days.of(span, mask, first), state} <> acc)
        case _:
          Crews{List.reverse(&2, T.Contractor, acc), Nil{}}

def Jobs.read(n: Nat, xs: List<&2, Nat>, +state: Nat, acc: List<&2, T.Appraisal>) -> List<&2, T.Appraisal>:
  match n:
    case 0n:
      List.reverse(&2, T.Appraisal, acc)
    case 1n+p:
      match xs:
        case id <> lat <> lon <> zip <> due <> m <> t:
          Jobs.read(p, t, state, T.Appraisal{id, T.Point{lat, lon}, zip, due, m, state} <> acc)
        case _:
          List.reverse(&2, T.Appraisal, acc)

def instance.got(c: Crews, +state: Nat, +cap: Nat, +first: Nat, +days: Nat, +jobs: Nat) -> Got:
  match c:
    case Crews{crews, rest}:
      Got{T.Instance{crews, Jobs.read(jobs, rest, state, Nil{}), cap, state, Tm.none()}, first, days}

def instance.empty() -> Got:
  Got{T.Instance{Nil{}, Nil{}, 0n, 0n, Tm.none()}, 0n, 0n}

def instance.version(ok: Bool, xs: List<&2, Nat>) -> Got:
  match ok:
    case False{}:
      instance.empty()
    case True{}:
      match xs:
        case +state <> +cap <> +first <> +days <> crews <> +jobs <> t:
          instance.got(Crews.read(crews, t, state, days, first, Nil{}), state, cap, first, days, jobs)
        case _:
          instance.empty()

# The words of instance.bin. A file in another format reads as an empty instance.
def instance(xs: List<&2, Nat>) -> Got:
  match xs:
    case v <> t:
      instance.version(Nat.is_eq(v, 1n), t)
    case Nil{}:
      instance.empty()

def Homes.keys(cs: List<&2, T.Contractor>, rest: List<&2, Nat>) -> List<&2, Nat>:
  match cs:
    case Nil{}:
      rest
    case c <> t:
      Tm.Point.key(T.Contractor.home(c)) <> Homes.keys(t, rest)

def Sites.keys(js: List<&2, T.Appraisal>) -> List<&2, Nat>:
  match js:
    case Nil{}:
      Nil{}
    case j <> t:
      Tm.Point.key(T.Appraisal.site(j)) <> Sites.keys(t)

# The points in the order points.bin lists them: homes, then sites.
def keys(+inst: T.Instance) -> List<&2, Nat>:
  Homes.keys(T.Instance.crews(inst), Sites.keys(T.Instance.jobs(inst)))

def with(+inst: T.Instance, times: T.Times) -> T.Instance:
  T.Instance{T.Instance.crews(inst), T.Instance.jobs(inst), T.Instance.cap(inst), T.Instance.state(inst), times}

# matrix.bin
# ----------

# from is the current row's point and rest the columns left in it. words counts
# every word read, the count included.
type Mx is Data:
  Mx{keys: List<&2, Nat>, from: Nat, rows: List<&2, Nat>, rest: List<&2, Nat>, cells: List<&2, Tm.Cell>, count: Nat, words: Nat}

def Mx.start(+keys: List<&2, Nat>) -> Mx:
  match keys:
    case Nil{}:
      Mx{Nil{}, 0n, Nil{}, Nil{}, Nil{}, 0n, 0n}
    case k <> t:
      Mx{keys, k, t, keys, Nil{}, 0n, 0n}

def Mx.keep(c: Bool, +from: Nat, +to: Nat, +ds: Nat, cells: List<&2, Tm.Cell>) -> List<&2, Tm.Cell>:
  match c:
    case True{}:
      Tm.Cell{from, to, Nat.div(Nat.add(ds, 599n), 600n)} <> cells
    case False{}:
      cells

def Mx.row(rows: List<&2, Nat>, +keys: List<&2, Nat>, cells: List<&2, Tm.Cell>, +count: Nat, +words: Nat) -> Mx:
  match rows:
    case Nil{}:
      Mx{keys, 0n, Nil{}, Nil{}, cells, count, words}
    case r <> t:
      Mx{keys, r, t, keys, cells, count, words}

def Mx.next(rest: List<&2, Nat>, rows: List<&2, Nat>, +keys: List<&2, Nat>, +from: Nat, cells: List<&2, Tm.Cell>, +count: Nat, +words: Nat) -> Mx:
  match rest:
    case Nil{}:
      Mx.row(rows, keys, cells, count, words)
    case o:
      Mx{keys, from, rows, o, cells, count, words}

def Mx.cell(rest: List<&2, Nat>, +w: Nat, +keys: List<&2, Nat>, +from: Nat, rows: List<&2, Nat>, cells: List<&2, Tm.Cell>, +count: Nat, +words: Nat) -> Mx:
  match rest:
    case Nil{}:
      Mx{keys, from, rows, Nil{}, cells, count, 1n+words}
    case +k <> t:
      +keep = Bool.and(Bool.not(Nat.is_eq(w, Unreachable())), Bool.not(Nat.is_eq(from, k)))
      Mx.next(t, rows, keys, from, Mx.keep(keep, from, k, w, cells), count, 1n+words)

def Mx.first(c: Bool, +w: Nat, +keys: List<&2, Nat>, +from: Nat, rows: List<&2, Nat>, rest: List<&2, Nat>, cells: List<&2, Tm.Cell>, +count: Nat, +words: Nat) -> Mx:
  match c:
    case True{}:
      Mx{keys, from, rows, rest, cells, w, 1n}
    case False{}:
      Mx.cell(rest, w, keys, from, rows, cells, count, words)

def Mx.word(+w: Nat, m: Mx) -> Mx:
  match m:
    case Mx{+keys, +from, rows, rest, cells, +count, +words}:
      Mx.first(Nat.is_eq(words, 0n), w, keys, from, rows, rest, cells, count, words)

def Mx.bytes(xs: List<&2, U32>, m: Mx) -> Mx:
  match xs:
    case +a <> +b <> +c <> +d <> t:
      Mx.bytes(t, Mx.word(le(a, b, c, d), m))
    case _:
      m

# The file held a time for every pair of the n points, and nothing more.
def Mx.ok(m: Mx, +n: Nat) -> Bool:
  match m:
    case Mx{_, _, _, _, _, +count, +words}:
      Bool.and(Nat.is_eq(count, n), Nat.is_eq(words, Nat.add(1n, Nat.mul(n, n))))

def Mx.reached(m: Mx) -> Nat:
  match m:
    case Mx{_, _, _, _, cells, _, _}:
      List.length(&2, Tm.Cell, cells)

# limit is the search limit in deciseconds, so a pair out of reach takes at
# least the next whole minute past it.
def Mx.times(m: Mx, +limit: Nat) -> T.Times:
  match m:
    case Mx{_, _, _, _, cells, _, _}:
      Tm.of.cells(Nat.add(Nat.div(limit, 600n), 1n), cells)

def Homes.points(cs: List<&2, T.Contractor>, rest: List<&2, T.Point>) -> List<&2, T.Point>:
  match cs:
    case Nil{}:
      rest
    case c <> t:
      T.Contractor.home(c) <> Homes.points(t, rest)

def Sites.points(js: List<&2, T.Appraisal>) -> List<&2, T.Point>:
  match js:
    case Nil{}:
      Nil{}
    case j <> t:
      T.Appraisal.site(j) <> Sites.points(t)

# The points themselves, in the same order as keys.
def points(+inst: T.Instance) -> List<&2, T.Point>:
  Homes.points(T.Instance.crews(inst), Sites.points(T.Instance.jobs(inst)))
