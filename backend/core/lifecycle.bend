import Base
import ./types.bend as T

type Action is Data:
  Start{}
  Complete{}
  Miss{}
  Retry{}
  Cancel{}

# A stop being worked or already done can't move, so healing must leave it alone.
def Status.locked(s: T.Status) -> Bool:
  match s:
    case T.Underway{}:
      True{}
    case T.Completed{}:
      True{}
    case o:
      False{}

def Status.is_open(s: T.Status) -> Bool:
  match s:
    case T.Open{}:
      True{}
    case o:
      False{}

def Status.is_underway(s: T.Status) -> Bool:
  match s:
    case T.Underway{}:
      True{}
    case o:
      False{}

# None{} means the action isn't allowed from that status.
def step(s: T.Status, a: Action) -> Maybe<&2, T.Status>:
  match s a:
    case T.Open{} Start{}:
      Some{T.Underway{}}
    case T.Open{} Cancel{}:
      Some{T.Cancelled{}}
    case T.Underway{} Complete{}:
      Some{T.Completed{}}
    case T.Underway{} Miss{}:
      Some{T.Failed{}}
    case T.Failed{} Retry{}:
      Some{T.Open{}}
    case T.Failed{} Cancel{}:
      Some{T.Cancelled{}}
    case _ _:
      None{}

def advance.next(s: T.Status, m: Maybe<&2, T.Status>) -> T.Status:
  match m:
    case None{}:
      s
    case Some{n}:
      n

# The status after an action, or the same status if it's refused.
def advance(+s: T.Status, a: Action) -> T.Status:
  advance.next(s, step(s, a))

# Refused actions are skipped, the way the event log will replay them.
def run(acts: List<&2, Action>, +s: T.Status) -> T.Status:
  match acts:
    case Nil{}:
      s
    case a <> t:
      run(t, advance(s, a))
