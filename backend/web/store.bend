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

# The lower 48 and DC, the only places Cloverleaf plans.
def Enums.states() -> List<&2, String>:
  ["AL", "AR", "AZ", "CA", "CO", "CT", "DC", "DE", "FL", "GA", "IA", "ID", "IL",
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

# organization is the dealer that requested it, the one whose key can read
# and cancel it.
def Schemas.appraisal() -> S.Schema:
  S.Schema.obj("Appraisal",
    S.SField{"id", S.SStr{},
      S.SField{"organization", S.SStr{},
        S.SField{"key", S.SStr{},
          S.SField{"address", S.SStr{},
            S.SField{"zip", S.SStr{},
              S.SField{"state", Schemas.state(),
                S.SField{"due", S.SStr{},
                  S.SField{"status", Schemas.status(), S.SEnd{}}}}}}}}})

# What an admin sends to add a dealer organization.
def Schemas.org.draft() -> S.Schema:
  S.Schema.obj("NewOrganization", S.SField{"name", S.SStr{}, S.SEnd{}})

# The answer to adding one. apiKey is shown this once: the store keeps only its
# hash.
def Schemas.org.key() -> S.Schema:
  S.Schema.obj("OrganizationKey",
    S.SField{"id", S.SStr{},
      S.SField{"name", S.SStr{},
        S.SField{"apiKey", S.SStr{}, S.SEnd{}}}})

# An organization as the log and the snapshot hold it, with its key's SHA-256
# in hex. Never sent to a client.
def Schemas.org.stored() -> S.Schema:
  S.Schema.obj("StoredOrganization",
    S.SField{"id", S.SStr{},
      S.SField{"name", S.SStr{},
        S.SField{"keyHash", S.SStr{}, S.SEnd{}}}})

# In the order of OrgStatus.tag: an active organization's key works, and a
# revoked one's doesn't.
def Enums.org.statuses() -> List<&2, String>:
  ["active", "revoked"]

def Schemas.org.status() -> S.Schema:
  S.SEnum{"OrganizationStatus", Enums.org.statuses()}

# An organization as an admin sees it, without its key.
def Schemas.org() -> S.Schema:
  S.Schema.obj("Organization",
    S.SField{"id", S.SStr{},
      S.SField{"name", S.SStr{},
        S.SField{"status", Schemas.org.status(), S.SEnd{}}}})

# One line of the log. Exactly one of the five fields is there. rekeyed holds
# an organization with its new key's hash, and revoked an organization's id.
# Both came after the first three, and a line from before them reads the same.
def Schemas.event() -> S.Schema:
  S.Schema.obj("Event",
    S.SOpt{"requested", Schemas.appraisal(),
      S.SOpt{"cancelled", S.SStr{},
        S.SOpt{"organized", Schemas.org.stored(),
          S.SOpt{"rekeyed", Schemas.org.stored(),
            S.SOpt{"revoked", S.SStr{}, S.SEnd{}}}}}})

# The first line of a snapshot: the store after the log's first `events`
# lines holds `organizations` organizations with a working key, then
# `revoked` organizations whose key was revoked, then `appraisals` records.
# `count` appraisals and `made` organizations were ever added, so ids aren't
# reused.
def Schemas.snapshot() -> S.Schema:
  S.Schema.obj("SnapshotHead",
    S.SField{"events", S.SNat{},
      S.SField{"count", S.SNat{},
        S.SField{"appraisals", S.SNat{},
          S.SField{"made", S.SNat{},
            S.SField{"organizations", S.SNat{},
              S.SField{"revoked", S.SNat{}, S.SEnd{}}}}}}})

def StateTag() -> Data:
  S.Tag(Enums.states())

def StatusTag() -> Data:
  S.Tag(Enums.statuses())

def OrgStatusTag() -> Data:
  S.Tag(Enums.org.statuses())

# The tag of an organization's status: active, or revoked when live is False.
def OrgStatus.tag(live: Bool) -> OrgStatusTag():
  match live:
    case True{}:
      Done{Unit{}}
    case False{}:
      Fail{Done{Unit{}}}

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

# A request as the store takes it: the body a dealer sent, and org, the
# organization whose key sent it. org never comes from the body.
type Draft is Data:
  Draft{org: String, key: String, address: String, zip: String, state: StateTag(), due: String}

type Rec is Data:
  Rec{id: String, org: String, key: String, address: String, zip: String, state: StateTag(), due: String, status: T.Status}

def Rec.id(r: Rec) -> String:
  match r:
    case Rec{i, o, k, a, z, st, d, s}:
      i

def Rec.org(r: Rec) -> String:
  match r:
    case Rec{i, o, k, a, z, st, d, s}:
      o

def Rec.key(r: Rec) -> String:
  match r:
    case Rec{i, o, k, a, z, st, d, s}:
      k

def Draft.org(d: Draft) -> String:
  match d:
    case Draft{o, k, a, z, st, due}:
      o

def Draft.key(d: Draft) -> String:
  match d:
    case Draft{o, k, a, z, st, due}:
      k

def Rec.status(r: Rec) -> T.Status:
  match r:
    case Rec{i, o, k, a, z, st, d, s}:
      s

def Rec.new(id: String, d: Draft) -> Rec:
  match d:
    case Draft{o, k, a, z, st, due}:
      Rec{id, o, k, a, z, st, due, T.Open{}}

def Rec.with(r: Rec, s: T.Status) -> Rec:
  match r:
    case Rec{i, o, k, a, z, st, d, old}:
      Rec{i, o, k, a, z, st, d, s}

def Draft.of(org: String, v: S.Value(Schemas.draft())) -> Draft:
  (k, r1) = v
  (a, r2) = r1
  (z, r3) = r2
  (st, r4) = r3
  (d, u) = r4
  Draft{org, k, a, z, st, d}

def Rec.value(r: Rec) -> S.Value(Schemas.appraisal()):
  match r:
    case Rec{i, o, k, a, z, st, d, s}:
      (i, (o, (k, (a, (z, (st, (d, (Status.tag(s), Unit{}))))))))

def Rec.of(v: S.Value(Schemas.appraisal())) -> Rec:
  (i, r0) = v
  (o, r1) = r0
  (k, r2) = r1
  (a, r3) = r2
  (z, r4) = r3
  (st, r5) = r4
  (d, r6) = r5
  (s, u) = r6
  Rec{i, o, k, a, z, st, d, Status.of(s)}

# Organizations
# -------------

# A dealer organization. hash is the SHA-256 of its API key, in hex.
type Org is Data:
  Org{id: String, name: String, hash: String}

def Org.id(g: Org) -> String:
  match g:
    case Org{i, n, h}:
      i

def Org.name(g: Org) -> String:
  match g:
    case Org{i, n, h}:
      n

def Org.hash(g: Org) -> String:
  match g:
    case Org{i, n, h}:
      h

# The organization as an admin sees it, active when live.
def Org.view(live: Bool, g: Org) -> S.Value(Schemas.org()):
  match g:
    case Org{i, n, h}:
      (i, (n, (OrgStatus.tag(live), Unit{})))

def Org.value(g: Org) -> S.Value(Schemas.org.stored()):
  match g:
    case Org{i, n, h}:
      (i, (n, (h, Unit{})))

def Org.of(v: S.Value(Schemas.org.stored())) -> Org:
  (i, r1) = v
  (n, r2) = r1
  (h, u) = r2
  Org{i, n, h}

def Orgs.pick(hit: Bool, g: Org, rest: Maybe<&2, Org>) -> Maybe<&2, Org>:
  match hit:
    case True{}:
      Some{g}
    case False{}:
      rest

# The organization whose key has this hash.
def Orgs.by_hash(+h: String, gs: List<&2, Org>) -> Maybe<&2, Org>:
  match gs:
    case Nil{}:
      None{}
    case Con{+g, rest}:
      Orgs.pick(J.Text.same(h, Org.hash(g)), g, Orgs.by_hash(h, rest))

# The organization with this id.
def Orgs.find(+i: String, gs: List<&2, Org>) -> Maybe<&2, Org>:
  match gs:
    case Nil{}:
      None{}
    case Con{+g, rest}:
      Orgs.pick(J.Text.same(i, Org.id(g)), g, Orgs.find(i, rest))

def Orgs.drop.pick(hit: Bool, g: Org, rest: List<&2, Org>) -> List<&2, Org>:
  match hit:
    case True{}:
      rest
    case False{}:
      g <> rest

# The organizations without any with this id.
def Orgs.drop(+i: String, gs: List<&2, Org>) -> List<&2, Org>:
  match gs:
    case Nil{}:
      []
    case Con{+g, rest}:
      Orgs.drop.pick(J.Text.same(i, Org.id(g)), g, Orgs.drop(i, rest))

# Whether some organization has this id and this key hash.
def Orgs.holds(+i: String, +h: String, gs: List<&2, Org>) -> Bool:
  match gs:
    case Nil{}:
      False{}
    case Con{+g, rest}:
      (J.Text.same(i, Org.id(g)) && J.Text.same(h, Org.hash(g))) || Orgs.holds(i, h, rest)

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

# s holds a control character: a code below 32, or 127.
def Text.control(s: String) -> Bool:
  match s:
    case SCon{+c, t}:
      Nat.is_lt(J.Text.code(c), 32n) || Nat.is_eq(J.Text.code(c), 127n) || Text.control(t)
    case SNil{}:
      False{}

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
    case Draft{o, k, a, z, st, due}:
      Draft.first(Text.sized(k, 1n, 64n), "invalid_key", "key must be 1 to 64 characters",
        Draft.first(Text.sized(a, 1n, 200n), "invalid_address", "address must be 1 to 200 characters",
          Draft.first(Text.digits(5n, z), "invalid_zip", "zip must be 5 digits",
            Draft.first(Date.ok(due), "invalid_due", "due must be a date, YYYY-MM-DD", None{}))))

# The first rule an organization's name breaks, or None.
def Org.problem(+name: String) -> Maybe<&2, Problem>:
  Draft.first(Text.sized(name, 1n, 100n), "invalid_name", "name must be 1 to 100 characters",
    Draft.first(Nat.is_lt(0n, String.length(String.trim(name))), "invalid_name", "name must not be blank",
      Draft.first(Bool.not(Text.control(name)), "invalid_name", "name must not hold control characters", None{})))

# Events and the store
# --------------------

# Appraisal ids are unique across organizations, so a cancel names only the
# id. The handler only cancels a record the caller's organization owns.
# Rekeyed gives an organization a new key's hash, and Revoked takes its key
# away. Only the admin does either.
type Change is Data:
  Requested{rec: Rec}
  Cancelled{id: String}
  Organized{org: Org}
  Rekeyed{org: Org}
  Revoked{id: String}

# Records newest first. orgs and retired put the organization changed last
# first: a new, rekeyed or reactivated one at the head of orgs, a revoked one
# at the head of retired. Order means nothing for organizations, since each is
# looked up by its id or key hash. count is how many appraisals were
# ever requested, so the next id is a+(count+1), and made is how many
# organizations were ever added, so the next is o+(made+1). Ids are never
# reused. orgs are the organizations whose key works, the only ones a key is
# looked up in, and retired are the ones whose key was revoked. An
# organization is in one list or the other, and keeps its appraisals either
# way.
type Store is Data:
  Store{count: Nat, recs: List<&2, Rec>, made: Nat, orgs: List<&2, Org>, retired: List<&2, Org>}

def Store.empty() -> Store:
  Store{0n, [], 0n, [], []}

def Store.count(s: Store) -> Nat:
  match s:
    case Store{n, rs, m, gs, rt}:
      n

def Store.recs(s: Store) -> List<&2, Rec>:
  match s:
    case Store{n, rs, m, gs, rt}:
      rs

def Store.made(s: Store) -> Nat:
  match s:
    case Store{n, rs, m, gs, rt}:
      m

def Store.orgs(s: Store) -> List<&2, Org>:
  match s:
    case Store{n, rs, m, gs, rt}:
      gs

def Store.retired(s: Store) -> List<&2, Org>:
  match s:
    case Store{n, rs, m, gs, rt}:
      rt

def Store.org.pick(live: Maybe<&2, Org>, gone: Maybe<&2, Org>) -> Maybe<&2, Org>:
  match live:
    case Some{g}:
      Some{g}
    case None{}:
      gone

# The organization with this id, whether its key works or was revoked.
def Store.org(+i: String, +s: Store) -> Maybe<&2, Org>:
  Store.org.pick(Orgs.find(i, Store.orgs(s)), Orgs.find(i, Store.retired(s)))

def Store.next(s: Store) -> String:
  "a" ++ Nat.show(Nat.add(Store.count(s), 1n))

def Store.next.org(s: Store) -> String:
  "o" ++ Nat.show(Nat.add(Store.made(s), 1n))

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

# The record with this id, if the organization org owns it. A dealer reads and
# cancels through this, so another dealer's record reads as missing.
def Store.owned(+org: String, +id: String, rs: List<&2, Rec>) -> Maybe<&2, Rec>:
  match rs:
    case Nil{}:
      None{}
    case Con{+r, rest}:
      Store.find.pick(J.Text.same(id, Rec.id(r)) && J.Text.same(org, Rec.org(r)), r, Store.owned(org, id, rest))

# The organization org's record with this key. Keys are each dealer's own, so
# two dealers can use the same one.
def Store.by_key(+org: String, +key: String, rs: List<&2, Rec>) -> Maybe<&2, Rec>:
  match rs:
    case Nil{}:
      None{}
    case Con{+r, rest}:
      Store.find.pick(J.Text.same(key, Rec.key(r)) && J.Text.same(org, Rec.org(r)), r, Store.by_key(org, key, rest))

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
    case Store{n, rs, m, gs, rt}:
      Store{n, Recs.cancel(i, rs), m, gs, rt}

def Store.put(r: Rec, s: Store) -> Store:
  match s:
    case Store{n, rs, m, gs, rt}:
      Store{Nat.add(n, 1n), r <> rs, m, gs, rt}

def Store.enroll(g: Org, s: Store) -> Store:
  match s:
    case Store{n, rs, m, gs, rt}:
      Store{n, rs, Nat.add(m, 1n), g <> gs, rt}

def Store.swap(+g: Org, s: Store) -> Store:
  match s:
    case Store{n, rs, m, gs, rt}:
      Store{n, rs, m, g <> Orgs.drop(Org.id(g), gs), Orgs.drop(Org.id(g), rt)}

# A new key for a stored organization: g, with its new hash, replaces it, and
# a revoked one is active again. A rekey for an id nobody has changes nothing.
def Store.rekey(found: Maybe<&2, Org>, +g: Org, s: Store) -> Store:
  match found:
    case None{}:
      s
    case Some{x}:
      Store.swap(g, s)

def Orgs.retire(found: Maybe<&2, Org>, rt: List<&2, Org>) -> List<&2, Org>:
  match found:
    case None{}:
      rt
    case Some{g}:
      g <> rt

# Revoking moves the organization with this id from orgs to retired, so no
# key is looked up in it any more. One that's already revoked, or that nobody
# has, stays as it is.
def Store.revoke(+i: String, s: Store) -> Store:
  match s:
    case Store{n, rs, +m, +gs, rt}:
      Store{n, rs, m, Orgs.drop(i, gs), Orgs.retire(Orgs.find(i, gs), rt)}

def Store.organize(found: Maybe<&2, Org>, g: Org, s: Store) -> Store:
  match found:
    case None{}:
      Store.enroll(g, s)
    case Some{x}:
      s

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
    case Organized{+g}:
      Store.organize(Store.org(Org.id(g), s), g, s)
    case Rekeyed{+g}:
      Store.rekey(Store.org(Org.id(g), s), g, s)
    case Revoked{i}:
      Store.revoke(i, s)

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
      (Some{Rec.value(r)}, (None{}, (None{}, (None{}, (None{}, Unit{})))))
    case Cancelled{i}:
      (None{}, (Some{i}, (None{}, (None{}, (None{}, Unit{})))))
    case Organized{g}:
      (None{}, (None{}, (Some{Org.value(g)}, (None{}, (None{}, Unit{})))))
    case Rekeyed{g}:
      (None{}, (None{}, (None{}, (Some{Org.value(g)}, (None{}, Unit{})))))
    case Revoked{i}:
      (None{}, (None{}, (None{}, (None{}, (Some{i}, Unit{})))))

def Change.pick(req: Maybe<&2, S.Value(Schemas.appraisal())>, can: Maybe<&2, String>, org: Maybe<&2, S.Value(Schemas.org.stored())>, rekey: Maybe<&2, S.Value(Schemas.org.stored())>, rev: Maybe<&2, String>) -> Maybe<&2, Change>:
  match req can org rekey rev:
    case Some{r} None{} None{} None{} None{}:
      Some{Requested{Rec.of(r)}}
    case None{} Some{i} None{} None{} None{}:
      Some{Cancelled{i}}
    case None{} None{} Some{g} None{} None{}:
      Some{Organized{Org.of(g)}}
    case None{} None{} None{} Some{g} None{}:
      Some{Rekeyed{Org.of(g)}}
    case None{} None{} None{} None{} Some{i}:
      Some{Revoked{i}}
    case _ _ _ _ _:
      None{}

def Change.of(v: S.Value(Schemas.event())) -> Maybe<&2, Change>:
  (req, r1) = v
  (can, r2) = r1
  (org, r3) = r2
  (rekey, r4) = r3
  (rev, u) = r4
  Change.pick(req, can, org, rekey, rev)

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

# A snapshot is a head line, then one organization per line, active ones
# then revoked ones, then one record per line, each in store order, so the shell writes and reads it a line at a
# time and never holds it whole. One cut off by a crash has fewer lines than
# its head says, and doesn't load.

type Snap is Data:
  Snap{events: Nat, store: Store}

type Head is Data:
  Head{events: Nat, count: Nat, size: Nat, made: Nat, orgs: Nat, retired: Nat}

def Head.value(n: Nat, c: Nat, k: Nat, m: Nat, o: Nat, r: Nat) -> S.Value(Schemas.snapshot()):
  (n, (c, (k, (m, (o, (r, Unit{}))))))

def Head.of(v: S.Value(Schemas.snapshot())) -> Head:
  (n, r1) = v
  (c, r2) = r1
  (k, r3) = r2
  (m, r4) = r3
  (o, r5) = r4
  (r, u) = r5
  Head{n, c, k, m, o, r}

def Head.orgs(h: Head) -> Nat:
  match h:
    case Head{n, c, k, m, o, r}:
      o

# How many organization lines come before the records.
def Head.all(h: Head) -> Nat:
  match h:
    case Head{n, c, k, m, o, r}:
      Nat.add(o, r)

def Snapshot.head(n: Nat, +s: Store) -> String:
  J.Json.print(S.encode(Schemas.snapshot(), Head.value(n, Store.count(s), List.length(&2, Rec, Store.recs(s)),
    Store.made(s), List.length(&2, Org, Store.orgs(s)), List.length(&2, Org, Store.retired(s))))) ++ "\n"

def Rec.line(r: Rec) -> String:
  J.Json.print(S.encode(Schemas.appraisal(), Rec.value(r))) ++ "\n"

def Org.line(g: Org) -> String:
  J.Json.print(S.encode(Schemas.org.stored(), Org.value(g))) ++ "\n"

def Org.found(m: Maybe<&2, S.Value(Schemas.org.stored())>) -> Maybe<&2, Org>:
  match m:
    case None{}:
      None{}
    case Some{v}:
      Some{Org.of(v)}

def Org.json(m: Maybe<&2, J.Json>) -> Maybe<&2, Org>:
  match m:
    case None{}:
      None{}
    case Some{j}:
      Org.found(S.decode(Schemas.org.stored(), j))

def Org.parse(line: String) -> Maybe<&2, Org>:
  Org.json(J.Json.parse(line))

def Head.found(m: Maybe<&2, S.Value(Schemas.snapshot())>) -> Maybe<&2, Head>:
  match m:
    case None{}:
      None{}
    case Some{v}:
      Some{Head.of(v)}

def Head.json(m: Maybe<&2, J.Json>) -> Maybe<&2, Head>:
  match m:
    case None{}:
      None{}
    case Some{j}:
      Head.found(S.decode(Schemas.snapshot(), j))

def Head.parse(line: String) -> Maybe<&2, Head>:
  Head.json(J.Json.parse(line))

def Rec.found(m: Maybe<&2, S.Value(Schemas.appraisal())>) -> Maybe<&2, Rec>:
  match m:
    case None{}:
      None{}
    case Some{v}:
      Some{Rec.of(v)}

def Rec.json(m: Maybe<&2, J.Json>) -> Maybe<&2, Rec>:
  match m:
    case None{}:
      None{}
    case Some{j}:
      Rec.found(S.decode(Schemas.appraisal(), j))

def Rec.parse(line: String) -> Maybe<&2, Rec>:
  Rec.json(J.Json.parse(line))

# Load state while the shell reads a snapshot in chunks of bytes. head is None
# until the head line is read. ok turns False at a line that isn't what the
# snapshot needs there, or that's longer than any record, and then the rest is
# ignored. got counts the lines read after the head: the first ones are
# organizations, active then revoked, as many as the head says, and the rest
# are records. orgs, gone and recs hold them oldest first, and line holds the
# bytes of the line being read, reversed, with width counting them.
type Load is Data:
  Load{head: Maybe<&2, Head>, ok: Bool, got: Nat, orgs: List<&2, Org>, gone: List<&2, Org>, recs: List<&2, Rec>, line: List<&2, U32>, width: Nat}

def Load.start() -> Load:
  Load{None{}, True{}, 0n, [], [], [], [], 0n}

def Load.broken() -> Load:
  Load{None{}, False{}, 0n, [], [], [], [], 0n}

def Load.rec(m: Maybe<&2, Rec>, h: Head, got: Nat, orgs: List<&2, Org>, gone: List<&2, Org>, recs: List<&2, Rec>) -> Load:
  match m:
    case Some{r}:
      Load{Some{h}, True{}, Nat.add(got, 1n), orgs, gone, r <> recs, [], 0n}
    case None{}:
      Load.broken()

def Load.org(m: Maybe<&2, Org>, h: Head, got: Nat, orgs: List<&2, Org>, gone: List<&2, Org>, recs: List<&2, Rec>) -> Load:
  match m:
    case Some{g}:
      Load{Some{h}, True{}, Nat.add(got, 1n), g <> orgs, gone, recs, [], 0n}
    case None{}:
      Load.broken()

def Load.retired(m: Maybe<&2, Org>, h: Head, got: Nat, orgs: List<&2, Org>, gone: List<&2, Org>, recs: List<&2, Rec>) -> Load:
  match m:
    case Some{g}:
      Load{Some{h}, True{}, Nat.add(got, 1n), orgs, g <> gone, recs, [], 0n}
    case None{}:
      Load.broken()

def Load.later(org: Bool, h: Head, got: Nat, orgs: List<&2, Org>, gone: List<&2, Org>, recs: List<&2, Rec>, text: String) -> Load:
  match org:
    case True{}:
      Load.retired(Org.parse(text), h, got, orgs, gone, recs)
    case False{}:
      Load.rec(Rec.parse(text), h, got, orgs, gone, recs)

def Load.kind(live: Bool, org: Bool, h: Head, got: Nat, orgs: List<&2, Org>, gone: List<&2, Org>, recs: List<&2, Rec>, text: String) -> Load:
  match live:
    case True{}:
      Load.org(Org.parse(text), h, got, orgs, gone, recs)
    case False{}:
      Load.later(org, h, got, orgs, gone, recs, text)

def Load.head(m: Maybe<&2, Head>) -> Load:
  match m:
    case Some{h}:
      Load{Some{h}, True{}, 0n, [], [], [], [], 0n}
    case None{}:
      Load.broken()

def Load.text(head: Maybe<&2, Head>, +got: Nat, orgs: List<&2, Org>, gone: List<&2, Org>, recs: List<&2, Rec>, text: String) -> Load:
  match head:
    case None{}:
      Load.head(Head.parse(text))
    case Some{+h}:
      Load.kind(Nat.is_lt(got, Head.orgs(h)), Nat.is_lt(got, Head.all(h)), h, got, orgs, gone, recs, text)

# The line just read ends.
def Load.end(ok: Bool, head: Maybe<&2, Head>, got: Nat, orgs: List<&2, Org>, gone: List<&2, Org>, recs: List<&2, Rec>, line: List<&2, U32>) -> Load:
  match ok:
    case True{}:
      Load.text(head, got, orgs, gone, recs, U.Utf8.decode(List.reverse(&2, U32, line)))
    case False{}:
      Load.broken()

def Load.grow(fits: Bool, b: U32, head: Maybe<&2, Head>, got: Nat, orgs: List<&2, Org>, gone: List<&2, Org>, recs: List<&2, Rec>, line: List<&2, U32>, width: Nat) -> Load:
  match fits:
    case True{}:
      Load{head, True{}, got, orgs, gone, recs, b <> line, Nat.add(width, 1n)}
    case False{}:
      Load.broken()

def Load.add(ok: Bool, b: U32, head: Maybe<&2, Head>, got: Nat, orgs: List<&2, Org>, gone: List<&2, Org>, recs: List<&2, Rec>, line: List<&2, U32>, +width: Nat) -> Load:
  match ok:
    case True{}:
      Load.grow(Nat.is_lt(width, 65536n), b, head, got, orgs, gone, recs, line, width)
    case False{}:
      Load.broken()

def Load.step(newline: Bool, b: U32, head: Maybe<&2, Head>, ok: Bool, got: Nat, orgs: List<&2, Org>, gone: List<&2, Org>, recs: List<&2, Rec>, line: List<&2, U32>, width: Nat) -> Load:
  match newline:
    case True{}:
      Load.end(ok, head, got, orgs, gone, recs, line)
    case False{}:
      Load.add(ok, b, head, got, orgs, gone, recs, line, width)

def Load.push(newline: Bool, b: U32, l: Load) -> Load:
  match l:
    case Load{head, ok, got, orgs, gone, recs, line, width}:
      Load.step(newline, b, head, ok, got, orgs, gone, recs, line, width)

def Load.feed.go(fuel: Nat, bs: List<&2, U32>, l: Load) -> Load:
  match fuel bs:
    case 0n _:
      l
    case 1n+f Nil{}:
      l
    case 1n+f Con{+b, rest}:
      Load.feed.go(f, rest, Load.push(Nat.is_eq(U32.to_nat(b), 10n), b, l))

def Load.feed(+bs: List<&2, U32>, l: Load) -> Load:
  Load.feed.go(List.length(&2, U32, bs), bs, l)

def Load.check(fits: Bool, n: Nat, c: Nat, m: Nat, orgs: List<&2, Org>, gone: List<&2, Org>, recs: List<&2, Rec>) -> Maybe<&2, Snap>:
  match fits:
    case True{}:
      Some{Snap{n, Store{c, List.reverse(&2, Rec, recs), m, List.reverse(&2, Org, orgs), List.reverse(&2, Org, gone)}}}
    case False{}:
      None{}

def Load.snap(head: Maybe<&2, Head>, +got: Nat, orgs: List<&2, Org>, gone: List<&2, Org>, recs: List<&2, Rec>) -> Maybe<&2, Snap>:
  match head:
    case None{}:
      None{}
    case Some{Head{n, +c, +k, +m, +o, +r}}:
      Load.check(Nat.is_eq(Nat.add(k, Nat.add(o, r)), got) && Nat.is_le(k, c) && Nat.is_le(Nat.add(o, r), m), n, c, m, orgs, gone, recs)

def Load.done(whole: Bool, head: Maybe<&2, Head>, got: Nat, orgs: List<&2, Org>, gone: List<&2, Org>, recs: List<&2, Rec>) -> Maybe<&2, Snap>:
  match whole:
    case True{}:
      Load.snap(head, got, orgs, gone, recs)
    case False{}:
      None{}

# The snapshot, once the whole file has been fed in, or None if it isn't one,
# like one a crash cut off while it was written.
def Load.finish(l: Load) -> Maybe<&2, Snap>:
  match l:
    case Load{head, ok, got, orgs, gone, recs, line, width}:
      Load.done(ok && List.is_empty(&2, U32, line), head, got, orgs, gone, recs)

# Replaying the log
# -----------------

# Replay state while the shell reads the log in chunks of bytes. lines counts
# the lines read so far, and the first skip of them are already in the
# snapshot the store started from. bad counts lines that weren't a change.
# line holds the bytes of the line being read, reversed, and width counts
# them. Only the first Replay.width() bytes of a line are kept, so a damaged log
# with a long run of bytes and no newline can't fill the memory. A line longer
# than that is a bad line. A real change is a few KB at most.
type Replay is Data:
  Replay{lines: Nat, skip: Nat, bad: Nat, store: Store, line: List<&2, U32>, width: Nat}

def Replay.width() -> Nat:
  65536n

def Replay.start(skip: Nat, s: Store) -> Replay:
  Replay{0n, skip, 0n, s, [], 0n}

def Replay.got(m: Maybe<&2, Change>, n: Nat, skip: Nat, bad: Nat, +s: Store) -> Replay:
  match m:
    case Some{c}:
      Replay{n, skip, bad, Store.apply(s, c), [], 0n}
    case None{}:
      Replay{n, skip, Nat.add(bad, 1n), s, [], 0n}

def Replay.parse(long: Bool, text: String) -> Maybe<&2, Change>:
  match long:
    case True{}:
      None{}
    case False{}:
      Change.parse(text)

def Replay.take(old: Bool, long: Bool, n: Nat, skip: Nat, bad: Nat, s: Store, text: String) -> Replay:
  match old:
    case True{}:
      Replay{n, skip, bad, s, [], 0n}
    case False{}:
      Replay.got(Replay.parse(long, text), n, skip, bad, s)

# The line just read ends.
def Replay.end(r: Replay) -> Replay:
  match r:
    case Replay{+n, +skip, bad, s, line, width}:
      Replay.take(Nat.is_lt(n, skip), Nat.is_lt(Replay.width(), width), Nat.add(n, 1n), skip, bad, s, U.Utf8.decode(List.reverse(&2, U32, line)))

# Keeps b only while the line is under the width, and counts it either way.
def Replay.grow(fits: Bool, b: U32, line: List<&2, U32>) -> List<&2, U32>:
  match fits:
    case True{}:
      b <> line
    case False{}:
      line

def Replay.push(newline: Bool, b: U32, r: Replay) -> Replay:
  match newline:
    case True{}:
      Replay.end(r)
    case False{}:
      match r:
        case Replay{n, skip, bad, s, line, +width}:
          Replay{n, skip, bad, s, Replay.grow(Nat.is_lt(width, Replay.width()), b, line), Nat.add(width, 1n)}

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
    case Replay{n, skip, bad, s, line, width}:
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
    case Replay{n, skip, bad, s, line, width}:
      n

def Replay.bad(r: Replay) -> Nat:
  match r:
    case Replay{n, skip, bad, s, line, width}:
      bad

def Replay.store(r: Replay) -> Store:
  match r:
    case Replay{n, skip, bad, s, line, width}:
      s

def Change.line(c: Change) -> String:
  J.Json.print(Change.write(c)) ++ "\n"

def Change.line.mend(torn: Bool, line: String) -> String:
  match torn:
    case True{}:
      "\n" ++ line
    case False{}:
      line

# A change's line, written after a write that failed partway when torn is
# True. It then starts with a newline, so a torn line the failure left stays a
# bad line of its own and can't swallow this change. A failure that wrote
# nothing leaves an empty line, which replay counts as a bad line.
def Change.line.after(torn: Bool, c: Change) -> String:
  Change.line.mend(torn, Change.line(c))
