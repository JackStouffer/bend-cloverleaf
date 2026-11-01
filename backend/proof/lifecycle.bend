import Base
import ../core/types.bend as T
import ../core/lifecycle.bend as Life
import ./logic.bend as L

def MS() -> Data:
  Maybe<&2, T.Status>

law completed_step:
  for +a: Life.Action
  {Life.step(T.Completed{}, a) == None{} : MS()}

def completed_step(a):
  match a:
    case Life.Start{}:
      {==}
    case Life.Complete{}:
      {==}
    case Life.Miss{}:
      {==}
    case Life.Retry{}:
      {==}
    case Life.Cancel{}:
      {==}

law cancelled_step:
  for +a: Life.Action
  {Life.step(T.Cancelled{}, a) == None{} : MS()}

def cancelled_step(a):
  match a:
    case Life.Start{}:
      {==}
    case Life.Complete{}:
      {==}
    case Life.Miss{}:
      {==}
    case Life.Retry{}:
      {==}
    case Life.Cancel{}:
      {==}

law completed_run:
  for +acts: List<&2, Life.Action>
  {Life.run(acts, T.Completed{}) == T.Completed{} : T.Status}

law next_same:
  for +a: Life.Action
  for +s: T.Status
  for +e: {Life.step(s, a) == None{} : MS()}
  {Life.advance(s, a) == s : T.Status}

def next_same(a, s, e):
  %Equal.sym(MS(), Life.step(s, a), None{}, e) : {Life.advance.next(s, _) == s : T.Status}
  {==}

def completed_run(acts):
  match acts:
    case Nil{}:
      {==}
    case +a <> t:
      %Equal.sym(T.Status, Life.advance(T.Completed{}, a), T.Completed{}, next_same(a, T.Completed{}, completed_step(a))) : {Life.run(t, _) == T.Completed{} : T.Status}
      completed_run(t)

law cancelled_run:
  for +acts: List<&2, Life.Action>
  {Life.run(acts, T.Cancelled{}) == T.Cancelled{} : T.Status}

def cancelled_run(acts):
  match acts:
    case Nil{}:
      {==}
    case +a <> t:
      %Equal.sym(T.Status, Life.advance(T.Cancelled{}, a), T.Cancelled{}, next_same(a, T.Cancelled{}, cancelled_step(a))) : {Life.run(t, _) == T.Cancelled{} : T.Status}
      cancelled_run(t)

law locked_cancel:
  for +s: T.Status
  for +e: {Life.Status.locked(s) == True{} : Bool}
  {Life.step(s, Life.Cancel{}) == None{} : MS()}

def locked_cancel(s, e):
  match s:
    case T.Underway{}:
      {==}
    case T.Completed{}:
      {==}
    case T.Open{}:
      L.never({Life.step(T.Open{}, Life.Cancel{}) == None{} : MS()}, e)
    case T.Failed{}:
      L.never({Life.step(T.Failed{}, Life.Cancel{}) == None{} : MS()}, e)
    case T.Cancelled{}:
      L.never({Life.step(T.Cancelled{}, Life.Cancel{}) == None{} : MS()}, e)

def IsDone(m: MS()) -> Bool:
  match m:
    case Some{T.Completed{}}:
      True{}
    case _:
      False{}

law not_done:
  for +m: MS()
  for -A: Type
  for +e: {m == Some{T.Completed{}} : MS()}
  for +f: {IsDone(m) == False{} : Bool}
  A

def not_done(m, A, e, f):
  L.never(A, Equal.trans(Bool, False{}, IsDone(m), True{}, Equal.sym(Bool, IsDone(m), False{}, f),
    Equal.cong(MS(), Bool, x => IsDone(x), m, Some{T.Completed{}}, e)))

law open_not_done:
  for +a: Life.Action
  {IsDone(Life.step(T.Open{}, a)) == False{} : Bool}

def open_not_done(a):
  match a:
    case Life.Start{}:
      {==}
    case Life.Complete{}:
      {==}
    case Life.Miss{}:
      {==}
    case Life.Retry{}:
      {==}
    case Life.Cancel{}:
      {==}

law failed_not_done:
  for +a: Life.Action
  {IsDone(Life.step(T.Failed{}, a)) == False{} : Bool}

def failed_not_done(a):
  match a:
    case Life.Start{}:
      {==}
    case Life.Complete{}:
      {==}
    case Life.Miss{}:
      {==}
    case Life.Retry{}:
      {==}
    case Life.Cancel{}:
      {==}

law only_underway:
  for +s: T.Status
  for +a: Life.Action
  for +e: {Life.step(s, a) == Some{T.Completed{}} : MS()}
  {s == T.Underway{} : T.Status}

def only_underway(s, a, e):
  match s:
    case T.Underway{}:
      {==}
    case T.Open{}:
      not_done(Life.step(T.Open{}, a), {T.Open{} == T.Underway{} : T.Status}, e, open_not_done(a))
    case T.Failed{}:
      not_done(Life.step(T.Failed{}, a), {T.Failed{} == T.Underway{} : T.Status}, e, failed_not_done(a))
    case T.Completed{}:
      not_done(Life.step(T.Completed{}, a), {T.Completed{} == T.Underway{} : T.Status}, e,
        %completed_step(a) : {IsDone(_) == False{} : Bool}
        {==})
    case T.Cancelled{}:
      not_done(Life.step(T.Cancelled{}, a), {T.Cancelled{} == T.Underway{} : T.Status}, e,
        %cancelled_step(a) : {IsDone(_) == False{} : Bool}
        {==})
