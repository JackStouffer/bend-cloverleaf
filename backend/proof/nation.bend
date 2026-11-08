import Base
import ../core/types.bend as T
import ../core/solve.bend as S
import ../core/nation.bend as N
import ./solve.bend as PS

# The national solve is a map of solve over the states, split and joined, so
# its laws come down to two facts about lists: splitting with take and drop and
# appending again loses nothing, and mapping over an append is appending maps.

def IL() -> Data:
  List<&2, T.Instance>

def PL() -> Data:
  List<&2, T.Plan>

def Seq(+xs: List<&2, T.Instance>, +tune: S.Tuning, +first: Nat, +last: Nat) -> List<&2, T.Plan>:
  N.national.seq(xs, tune, first, last)

law seq_append:
  for +xs: IL()
  for +ys: IL()
  for +tune: S.Tuning
  for +first: Nat
  for +last: Nat
  {Seq(List.append(&2, T.Instance, xs, ys), tune, first, last) == List.append(&2, T.Plan, Seq(xs, tune, first, last), Seq(ys, tune, first, last)) : PL()}

def seq_append(xs, ys, tune, first, last):
  match xs:
    case Nil{}:
      {==}
    case +h <> t:
      +p = S.solve(tune, h, first, last)
      %seq_append(t, ys, tune, first, last) : {p <> Seq(List.append(&2, T.Instance, t, ys), tune, first, last) == p <> _ : PL()}
      {==}

law national_seq:
  for +fuel: Nat
  for +tune: S.Tuning
  for +xs: IL()
  for +first: Nat
  for +last: Nat
  {N.national(fuel, tune, xs, first, last) == Seq(xs, tune, first, last) : PL()}

def national_seq(fuel, tune, xs, first, last):
  match fuel:
    case 0n:
      {==}
    case 1n+f:
      +at = N.States.split_at(xs, Nat.div(N.States.work(xs), 2n), 0n)
      +l = List.take(&2, T.Instance, xs, at)
      +r = List.drop(&2, T.Instance, xs, at)
      +nl = N.national(f, tune, l, first, last)
      +nr = N.national(f, tune, r, first, last)
      %Equal.sym(PL(), nl, Seq(l, tune, first, last), national_seq(f, tune, l, first, last)) : {List.append(&2, T.Plan, _, nr) == Seq(xs, tune, first, last) : PL()}
      %Equal.sym(PL(), nr, Seq(r, tune, first, last), national_seq(f, tune, r, first, last)) : {List.append(&2, T.Plan, Seq(l, tune, first, last), _) == Seq(xs, tune, first, last) : PL()}
      Equal.trans(PL(), List.append(&2, T.Plan, Seq(l, tune, first, last), Seq(r, tune, first, last)), Seq(List.append(&2, T.Instance, l, r), tune, first, last), Seq(xs, tune, first, last),
        Equal.sym(PL(), Seq(List.append(&2, T.Instance, l, r), tune, first, last), List.append(&2, T.Plan, Seq(l, tune, first, last), Seq(r, tune, first, last)), seq_append(l, r, tune, first, last)),
        Equal.cong(IL(), PL(), ys => Seq(ys, tune, first, last), List.append(&2, T.Instance, l, r), xs, PS.take_drop(T.Instance, xs, at)))

law seq_length:
  for +xs: IL()
  for +tune: S.Tuning
  for +first: Nat
  for +last: Nat
  {List.length(&2, T.Plan, Seq(xs, tune, first, last)) == List.length(&2, T.Instance, xs) : Nat}

def seq_length(xs, tune, first, last):
  match xs:
    case Nil{}:
      {==}
    case +h <> t:
      %seq_length(t, tune, first, last) : {1n+List.length(&2, T.Plan, Seq(t, tune, first, last)) == 1n+_ : Nat}
      {==}

def Plan.of(m: Maybe<&2, T.Instance>, +tune: S.Tuning, +first: Nat, +last: Nat) -> Maybe<&2, T.Plan>:
  match m:
    case None{}:
      None{}
    case Some{i}:
      Some{S.solve(tune, i, first, last)}

# Plan n of the map is the solve of state n.
law seq_get:
  for +xs: IL()
  for +n: Nat
  for +tune: S.Tuning
  for +first: Nat
  for +last: Nat
  {List.get(&2, T.Plan, Seq(xs, tune, first, last), n) == Plan.of(List.get(&2, T.Instance, xs, n), tune, first, last) : Maybe<&2, T.Plan>}

def seq_get(xs, n, tune, first, last):
  match xs:
    case Nil{}:
      match n:
        case 0n:
          {==}
        case 1n+p:
          {==}
    case +h <> t:
      match n:
        case 0n:
          {==}
        case 1n+p:
          seq_get(t, p, tune, first, last)

def MP() -> Data:
  Maybe<&2, T.Plan>
