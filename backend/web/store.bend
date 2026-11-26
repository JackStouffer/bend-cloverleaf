import Base

import ../core/types.bend as T
import ../core/lifecycle.bend as Life
import ./json.bend as J
import ./schema.bend as S
import ./utf8.bend as U

# Appraisal requests as the web process stores them: an append-only log of
# events, and the store that replaying it builds. Pure, so the laws cover the
# replay and the codecs for the log and the snapshot. web/main.bend does the
# file work.

# Enums
# -----

# The lower 48, the only states Cloverleaf plans.
def Enums.states() -> List<&2, String>:
  ["AL", "AR", "AZ", "CA", "CO", "CT", "DE", "FL", "GA", "IA", "ID", "IL",
   "IN", "KS", "KY", "LA", "MA", "MD", "ME", "MI", "MN", "MO", "MS", "MT",
   "NC", "ND", "NE", "NH", "NJ", "NM", "NV", "NY", "OH", "OK", "OR", "PA",
   "RI", "SC", "SD", "TN", "TX", "UT", "VA", "VT", "WA", "WI", "WV", "WY"]

# In the order of T.Status.
def Enums.statuses() -> List<&2, String>:
  ["open", "underway", "completed", "failed", "cancelled"]

def Schemas.state() -> S.Schema:
  S.SEnum{"UsState", Enums.states()}

def Schemas.status() -> S.Schema:
  S.SEnum{"AppraisalStatus", Enums.statuses()}

# What a dealer sends to request an appraisal. key is the dealer's own name for
# the request, so sending it again is safe. due is a date, YYYY-MM-DD.
def Schemas.draft() -> S.Schema:
  S.Schema.obj("NewAppraisal",
    S.SField{"key", S.SStr{},
      S.SField{"address", S.SStr{},
        S.SField{"zip", S.SStr{},
          S.SField{"state", Schemas.state(),
            S.SField{"due", S.SStr{}, S.SEnd{}}}}}})

def Schemas.appraisal() -> S.Schema:
  S.Schema.obj("Appraisal",
    S.SField{"id", S.SStr{},
      S.SField{"key", S.SStr{},
        S.SField{"address", S.SStr{},
          S.SField{"zip", S.SStr{},
            S.SField{"state", Schemas.state(),
              S.SField{"due", S.SStr{},
                S.SField{"status", Schemas.status(), S.SEnd{}}}}}}}})

# One line of the log. Exactly one of the two fields is there.
def Schemas.event() -> S.Schema:
  S.Schema.obj("Event",
    S.SOpt{"requested", Schemas.appraisal(),
      S.SOpt{"cancelled", S.SStr{}, S.SEnd{}}})

# The store after the log's first `events` lines.
def Schemas.snapshot() -> S.Schema:
  S.Schema.obj("Snapshot",
    S.SField{"events", S.SNat{},
      S.SField{"count", S.SNat{},
        S.SField{"appraisals", S.Schema.list(Schemas.appraisal()), S.SEnd{}}}})

def StateTag() -> Data:
  S.Tag(Enums.states())

def StatusTag() -> Data:
  S.Tag(Enums.statuses())

def Status.tag(s: T.Status) -> StatusTag():
  match s:
    case T.Open{}:
      Done{Unit{}}
    case T.Underway{}:
      Fail{Done{Unit{}}}
    case T.Completed{}:
      Fail{Fail{Done{Unit{}}}}
    case T.Failed{}:
      Fail{Fail{Fail{Done{Unit{}}}}}
    case T.Cancelled{}:
      Fail{Fail{Fail{Fail{Done{Unit{}}}}}}

def Status.of(t: StatusTag()) -> T.Status:
  match t:
    case Done{u}:
      T.Open{}
    case Fail{Done{u}}:
      T.Underway{}
    case Fail{Fail{Done{u}}}:
      T.Completed{}
    case Fail{Fail{Fail{Done{u}}}}:
      T.Failed{}
    case Fail{Fail{Fail{Fail{Done{u}}}}}:
      T.Cancelled{}
    case Fail{Fail{Fail{Fail{Fail{x}}}}}:
      Empty.absurd(T.Status, x)

def Status.is_cancelled(s: T.Status) -> Bool:
  match s:
    case T.Cancelled{}:
      True{}
    case other:
      False{}

# Records
# -------

type Draft is Data:
  Draft{key: String, address: String, zip: String, state: StateTag(), due: String}

type Rec is Data:
  Rec{id: String, key: String, address: String, zip: String, state: StateTag(), due: String, status: T.Status}

def Rec.id(r: Rec) -> String:
  match r:
    case Rec{i, k, a, z, st, d, s}:
      i

def Rec.key(r: Rec) -> String:
  match r:
    case Rec{i, k, a, z, st, d, s}:
      k

def Draft.key(d: Draft) -> String:
  match d:
    case Draft{k, a, z, st, due}:
      k

def Rec.status(r: Rec) -> T.Status:
  match r:
    case Rec{i, k, a, z, st, d, s}:
      s

def Rec.new(id: String, d: Draft) -> Rec:
  match d:
    case Draft{k, a, z, st, due}:
      Rec{id, k, a, z, st, due, T.Open{}}

def Rec.with(r: Rec, s: T.Status) -> Rec:
  match r:
    case Rec{i, k, a, z, st, d, old}:
      Rec{i, k, a, z, st, d, s}

def Draft.of(v: S.Value(Schemas.draft())) -> Draft:
  (k, r1) = v
  (a, r2) = r1
  (z, r3) = r2
  (st, r4) = r3
  (d, u) = r4
  Draft{k, a, z, st, d}

def Rec.value(r: Rec) -> S.Value(Schemas.appraisal()):
  match r:
    case Rec{i, k, a, z, st, d, s}:
      (i, (k, (a, (z, (st, (d, (Status.tag(s), Unit{})))))))

def Rec.of(v: S.Value(Schemas.appraisal())) -> Rec:
  (i, r1) = v
  (k, r2) = r1
  (a, r3) = r2
  (z, r4) = r3
  (st, r5) = r4
  (d, r6) = r5
  (s, u) = r6
  Rec{i, k, a, z, st, d, Status.of(s)}

# Checking a draft
# ----------------

def Text.digit(+c: Char) -> Bool:
  Nat.is_le(48n, J.Text.code(c)) && Nat.is_le(J.Text.code(c), 57n)

# s is exactly n ASCII digits.
def Text.digits(n: Nat, s: String) -> Bool:
  match n s:
    case 0n SNil{}:
      True{}
    case 1n+m SCon{+c, t}:
      Text.digit(c) && Text.digits(m, t)
    case _ _:
      False{}

def Text.between(+n: Nat, lo: Nat, hi: Nat) -> Bool:
  Nat.is_le(lo, n) && Nat.is_le(n, hi)

def Text.sized(s: String, lo: Nat, hi: Nat) -> Bool:
  Text.between(String.length(s), lo, hi)

def Date.within(m: Maybe<&2, Nat>, hi: Nat) -> Bool:
  match m:
    case Some{n}:
      Text.between(n, 1n, hi)
    case None{}:
      False{}

def Date.parts(ps: List<&2, String>) -> Bool:
  match ps:
    case Con{y, Con{+m, Con{+d, Nil{}}}}:
      Text.digits(4n, y) && Text.digits(2n, m) && Text.digits(2n, d)
        && Date.within(Nat.read(m), 12n) && Date.within(Nat.read(d), 31n)
    case other:
      False{}

# YYYY-MM-DD with a month from 01 to 12 and a day from 01 to 31. Whether the
# day exists in that month is left to planning, which works in day numbers.
def Date.ok(s: String) -> Bool:
  Date.parts(String.split(s, J.Text.char(45n)))

# A broken rule: a stable code for programs and a detail for people.
type Problem is Data:
  Problem{code: String, detail: String}

def Draft.first(ok: Bool, code: String, detail: String, rest: Maybe<&2, Problem>) -> Maybe<&2, Problem>:
  match ok:
    case True{}:
      rest
    case False{}:
      Some{Problem{code, detail}}

# The first rule the draft breaks, or None.
def Draft.problem(d: Draft) -> Maybe<&2, Problem>:
  match d:
    case Draft{k, a, z, st, due}:
      Draft.first(Text.sized(k, 1n, 64n), "invalid_key", "key must be 1 to 64 characters",
        Draft.first(Text.sized(a, 1n, 200n), "invalid_address", "address must be 1 to 200 characters",
          Draft.first(Text.digits(5n, z), "invalid_zip", "zip must be 5 digits",
            Draft.first(Date.ok(due), "invalid_due", "due must be a date, YYYY-MM-DD", None{}))))

# Events and the store
# --------------------

type Change is Data:
  Requested{rec: Rec}
  Cancelled{id: String}

# Records newest first. count is how many were ever requested, so the next id
# is a+(count+1) and ids are never reused.
type Store is Data:
  Store{count: Nat, recs: List<&2, Rec>}

def Store.empty() -> Store:
  Store{0n, []}

def Store.count(s: Store) -> Nat:
  match s:
    case Store{n, rs}:
      n

def Store.recs(s: Store) -> List<&2, Rec>:
  match s:
    case Store{n, rs}:
      rs

def Store.next(s: Store) -> String:
  "a" ++ Nat.show(Nat.add(Store.count(s), 1n))

def Store.find.pick(hit: Bool, r: Rec, rest: Maybe<&2, Rec>) -> Maybe<&2, Rec>:
  match hit:
    case True{}:
      Some{r}
    case False{}:
      rest

# The record with this id.
def Store.find(+id: String, rs: List<&2, Rec>) -> Maybe<&2, Rec>:
  match rs:
    case Nil{}:
      None{}
    case Con{+r, rest}:
      Store.find.pick(J.Text.same(id, Rec.id(r)), r, Store.find(id, rest))

# The record with this key.
def Store.by_key(+key: String, rs: List<&2, Rec>) -> Maybe<&2, Rec>:
  match rs:
    case Nil{}:
      None{}
    case Con{+r, rest}:
      Store.find.pick(J.Text.same(key, Rec.key(r)), r, Store.by_key(key, rest))

def Rec.cancel(+r: Rec) -> Rec:
  Rec.with(r, Life.advance(Rec.status(r), Life.Cancel{}))

def Recs.cancel.pick(hit: Bool, r: Rec, rest: List<&2, Rec>) -> List<&2, Rec>:
  match hit:
    case True{}:
      Rec.cancel(r) <> rest
    case False{}:
      r <> rest

# Cancels the record with this id, where the lifecycle allows it.
def Recs.cancel(+id: String, rs: List<&2, Rec>) -> List<&2, Rec>:
  match rs:
    case Nil{}:
      []
    case Con{+r, rest}:
      Recs.cancel.pick(J.Text.same(id, Rec.id(r)), r, Recs.cancel(id, rest))

def Store.cancel(+i: String, s: Store) -> Store:
  match s:
    case Store{n, rs}:
      Store{n, Recs.cancel(i, rs)}

def Store.put(r: Rec, s: Store) -> Store:
  match s:
    case Store{n, rs}:
      Store{Nat.add(n, 1n), r <> rs}

def Store.add(found: Maybe<&2, Rec>, r: Rec, s: Store) -> Store:
  match found:
    case None{}:
      Store.put(r, s)
    case Some{x}:
      s

# A request for an id that's already stored changes nothing, so replaying a
# log twice over gives the same store.
def Store.apply(+s: Store, e: Change) -> Store:
  match e:
    case Requested{+r}:
      Store.add(Store.find(Rec.id(r), Store.recs(s)), r, s)
    case Cancelled{i}:
      Store.cancel(i, s)

# The store after the changes es, in order, starting from s.
def Store.replay(es: List<&2, Change>, s: Store) -> Store:
  match es:
    case Nil{}:
      s
    case Con{e, rest}:
      Store.replay(rest, Store.apply(s, e))

# The log
# -------

def Change.value(e: Change) -> S.Value(Schemas.event()):
  match e:
    case Requested{r}:
      (Some{Rec.value(r)}, (None{}, Unit{}))
    case Cancelled{i}:
      (None{}, (Some{i}, Unit{}))

def Change.pick(req: Maybe<&2, S.Value(Schemas.appraisal())>, can: Maybe<&2, String>) -> Maybe<&2, Change>:
  match req can:
    case Some{r} None{}:
      Some{Requested{Rec.of(r)}}
    case None{} Some{i}:
      Some{Cancelled{i}}
    case _ _:
      None{}

def Change.of(v: S.Value(Schemas.event())) -> Maybe<&2, Change>:
  (req, r1) = v
  (can, u) = r1
  Change.pick(req, can)

def Change.write(e: Change) -> J.Json:
  S.encode(Schemas.event(), Change.value(e))

def Change.found(m: Maybe<&2, S.Value(Schemas.event())>) -> Maybe<&2, Change>:
  match m:
    case None{}:
      None{}
    case Some{v}:
      Change.of(v)

def Change.read(j: J.Json) -> Maybe<&2, Change>:
  Change.found(S.decode(Schemas.event(), j))

# A line of the log, or None for a line that isn't an event, like one cut off
# by a crash.
def Change.parsed(m: Maybe<&2, J.Json>) -> Maybe<&2, Change>:
  match m:
    case None{}:
      None{}
    case Some{j}:
      Change.read(j)

def Change.parse(line: String) -> Maybe<&2, Change>:
  Change.parsed(J.Json.parse(line))

# Snapshots
# ---------

type Snap is Data:
  Snap{events: Nat, store: Store}

def Recs.values(rs: List<&2, Rec>) -> List<&2, S.Value(Schemas.appraisal())>:
  match rs:
    case Nil{}:
      []
    case Con{r, rest}:
      Rec.value(r) <> Recs.values(rest)

def Recs.of(vs: List<&2, S.Value(Schemas.appraisal())>) -> List<&2, Rec>:
  match vs:
    case Nil{}:
      []
    case Con{v, rest}:
      Rec.of(v) <> Recs.of(rest)

def Snap.value(n: Nat, s: Store) -> S.Value(Schemas.snapshot()):
  match s:
    case Store{c, rs}:
      (n, (c, (Recs.values(rs), Unit{})))

def Snap.of(v: S.Value(Schemas.snapshot())) -> Snap:
  (n, r1) = v
  (c, r2) = r1
  (vs, u) = r2
  Snap{n, Store{c, Recs.of(vs)}}

def Snapshot.write(n: Nat, s: Store) -> J.Json:
  S.encode(Schemas.snapshot(), Snap.value(n, s))

def Snapshot.found(m: Maybe<&2, S.Value(Schemas.snapshot())>) -> Maybe<&2, Snap>:
  match m:
    case None{}:
      None{}
    case Some{v}:
      Some{Snap.of(v)}

def Snapshot.read(j: J.Json) -> Maybe<&2, Snap>:
  Snapshot.found(S.decode(Schemas.snapshot(), j))

# Replaying the log
# -----------------

# Replay state while the shell reads the log in chunks of bytes. lines counts
# the lines read so far, and the first skip of them are already in the
# snapshot the store started from. bad counts lines that weren't a change.
# line holds the bytes of the line being read, reversed.
type Replay is Data:
  Replay{lines: Nat, skip: Nat, bad: Nat, store: Store, line: List<&2, U32>}

def Replay.start(skip: Nat, s: Store) -> Replay:
  Replay{0n, skip, 0n, s, []}

def Replay.got(m: Maybe<&2, Change>, n: Nat, skip: Nat, bad: Nat, +s: Store) -> Replay:
  match m:
    case Some{c}:
      Replay{n, skip, bad, Store.apply(s, c), []}
    case None{}:
      Replay{n, skip, Nat.add(bad, 1n), s, []}

def Replay.take(old: Bool, n: Nat, skip: Nat, bad: Nat, s: Store, text: String) -> Replay:
  match old:
    case True{}:
      Replay{n, skip, bad, s, []}
    case False{}:
      Replay.got(Change.parse(text), n, skip, bad, s)

# The line just read ends.
def Replay.end(r: Replay) -> Replay:
  match r:
    case Replay{+n, +skip, bad, s, line}:
      Replay.take(Nat.is_lt(n, skip), Nat.add(n, 1n), skip, bad, s, U.Utf8.decode(List.reverse(&2, U32, line)))

def Replay.push(newline: Bool, b: U32, r: Replay) -> Replay:
  match newline:
    case True{}:
      Replay.end(r)
    case False{}:
      match r:
        case Replay{n, skip, bad, s, line}:
          Replay{n, skip, bad, s, b <> line}

def Replay.feed.go(fuel: Nat, bs: List<&2, U32>, r: Replay) -> Replay:
  match fuel bs:
    case 0n _:
      r
    case 1n+f Nil{}:
      r
    case 1n+f Con{+b, rest}:
      Replay.feed.go(f, rest, Replay.push(Nat.is_eq(U32.to_nat(b), 10n), b, r))

def Replay.feed(+bs: List<&2, U32>, r: Replay) -> Replay:
  Replay.feed.go(List.length(&2, U32, bs), bs, r)

# Whether a line was left without its newline at the end of the log, as a
# crash in the middle of a write leaves one.
def Replay.torn(r: Replay) -> Bool:
  match r:
    case Replay{n, skip, bad, s, line}:
      Bool.not(List.is_empty(&2, U32, line))

def Replay.cut(torn: Bool, r: Replay) -> Replay:
  match torn:
    case True{}:
      Replay.end(r)
    case False{}:
      r

# At the end of the log, a torn line counts as a line, so the shell ends it
# with a newline before it appends.
def Replay.finish(+r: Replay) -> Replay:
  Replay.cut(Replay.torn(r), r)

def Replay.lines(r: Replay) -> Nat:
  match r:
    case Replay{n, skip, bad, s, line}:
      n

def Replay.bad(r: Replay) -> Nat:
  match r:
    case Replay{n, skip, bad, s, line}:
      bad

def Replay.store(r: Replay) -> Store:
  match r:
    case Replay{n, skip, bad, s, line}:
      s

def Snapshot.parsed(m: Maybe<&2, J.Json>) -> Maybe<&2, Snap>:
  match m:
    case None{}:
      None{}
    case Some{j}:
      Snapshot.read(j)

# The snapshot file's text, or None if it isn't a snapshot, like one cut off
# by a crash while it was written.
def Snapshot.parse(text: String) -> Maybe<&2, Snap>:
  Snapshot.parsed(J.Json.parse(text))

def Snapshot.text(n: Nat, s: Store) -> String:
  J.Json.print(Snapshot.write(n, s))

def Change.line(c: Change) -> String:
  J.Json.print(Change.write(c)) ++ "\n"
