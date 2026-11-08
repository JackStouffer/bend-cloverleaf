import Base
import ./types.bend as T
import ./solve.bend as S

# The nightly national solve. Contractors never cross a state line, so each
# state is its own instance and its own solve, and nothing one state does can
# change another's plan.
#
# States fork by estimated work, never by count: California holds about a third
# of the national work and Wyoming almost none, and Bend never moves a task once
# it's assigned. Each state's solve forks again inside.

# Assigning a job searches every route, so a state's work grows with jobs times
# contractors. The 1 keeps an empty state from costing nothing.
def State.work(+inst: T.Instance) -> Nat:
  Nat.add(1n, Nat.mul(List.length(&2, T.Appraisal, T.Instance.jobs(inst)), List.length(&2, T.Contractor, T.Instance.crews(inst))))

def States.work(xs: List<&2, T.Instance>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case +i <> t:
      Nat.add(State.work(i), States.work(t))

def split_at.if(c: Bool, +at: Nat, next: Unit -> Nat) -> Nat:
  match c:
    case True{}:
      Nat.max(at, 1n)
    case False{}:
      next(Unit{})

# How many states from the front hold half the work.
def States.split_at(xs: List<&2, T.Instance>, +half: Nat, +at: Nat) -> Nat:
  match xs:
    case Nil{}:
      at
    case +i <> t:
      split_at.if(Nat.is_ge(State.work(i), half), at, u => States.split_at(t, Nat.sub(half, State.work(i)), 1n+at))

# One state after another, which is what the parallel solve must match.
def national.seq(xs: List<&2, T.Instance>, +tune: S.Tuning, +first: Nat, +last: Nat) -> List<&2, T.Plan>:
  match xs:
    case Nil{}:
      Nil{}
    case +i <> t:
      S.solve(tune, i, first, last) <> national.seq(t, tune, first, last)

# Every state's plan, in the order the states came in. fuel is how many times
# the states split in two.
def national(+fuel: Nat, +tune: S.Tuning, +xs: List<&2, T.Instance>, +first: Nat, +last: Nat) -> List<&2, T.Plan>:
  match fuel:
    case 0n:
      national.seq(xs, tune, first, last)
    case 1n+f:
      +at = States.split_at(xs, Nat.div(States.work(xs), 2n), 0n)
      a b = national(f, tune, List.take(&2, T.Instance, xs, at), first, last) national(f, tune, List.drop(&2, T.Instance, xs, at), first, last)
      List.append(&2, T.Plan, a, b)
