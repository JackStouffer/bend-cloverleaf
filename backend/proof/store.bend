import Base
import ../core/types.bend as T
import ../core/lifecycle.bend as Life
import ../web/json.bend as J
import ../web/schema.bend as S
import ../web/store.bend as St
import ../web/api.bend as A
import ./logic.bend as L
import ./web.bend as PW

# Proofs about the appraisal store and its log, and the handlers that change
# them. LAWS.bend states the rules; these prove them.

def MS() -> Data:
  Maybe<&2, St.Rec>

def MC() -> Data:
  Maybe<&2, St.Change>

# Replay
# ------

law replay_append:
  for +xs: List<&2, St.Change>
  for +ys: List<&2, St.Change>
  for +s: St.Store
  {St.Store.replay(List.append(&2, St.Change, xs, ys), s) == St.Store.replay(ys, St.Store.replay(xs, s)) : St.Store}

def replay_append(xs, ys, s):
  match xs:
    case Nil{}:
      {==}
    case Con{e, rest}:
      replay_append(rest, ys, St.Store.apply(s, e))

law replay_resumes:
  for +es: List<&2, St.Change>
  for +n: Nat
  for +s: St.Store
  {St.Store.replay(List.drop(&2, St.Change, es, n), St.Store.replay(List.take(&2, St.Change, es, n), s)) == St.Store.replay(es, s) : St.Store}

def replay_resumes(es, n, s):
  match es n:
    case Nil{} _:
      {==}
    case Con{e, rest} 0n:
      {==}
    case Con{e, rest} 1n+m:
      replay_resumes(rest, m, St.Store.apply(s, e))

law put_finds:
  for +r: St.Rec
  for +s: St.Store
  {St.Store.find(St.Rec.id(r), St.Store.recs(St.Store.put(r, s))) == Some{r} : MS()}

def put_finds(r, s):
  match s:
    case St.Store{n, rs, m, gs, rt}:
      %Equal.sym(Bool, J.Text.same(St.Rec.id(r), St.Rec.id(r)), True{}, PW.same_refl(St.Rec.id(r))) : {St.Store.find.pick(_, r, St.Store.find(St.Rec.id(r), rs)) == Some{r} : MS()}
      {==}

law request_is_stored:
  for +s: St.Store
  for +r: St.Rec
  for +fresh: {St.Store.find(St.Rec.id(r), St.Store.recs(s)) == None{} : MS()}
  {St.Store.find(St.Rec.id(r), St.Store.recs(St.Store.apply(s, St.Requested{r}))) == Some{r} : MS()}

def request_is_stored(s, r, fresh):
  %Equal.sym(MS(), St.Store.find(St.Rec.id(r), St.Store.recs(s)), None{}, fresh) : {St.Store.find(St.Rec.id(r), St.Store.recs(St.Store.add(_, r, s))) == Some{r} : MS()}
  put_finds(r, s)

law request_again_changes_nothing:
  for +s: St.Store
  for +r: St.Rec
  for +x: St.Rec
  for +known: {St.Store.find(St.Rec.id(r), St.Store.recs(s)) == Some{x} : MS()}
  {St.Store.apply(s, St.Requested{r}) == s : St.Store}

def request_again_changes_nothing(s, r, x, known):
  %Equal.sym(MS(), St.Store.find(St.Rec.id(r), St.Store.recs(s)), Some{x}, known) : {St.Store.add(_, r, s) == s : St.Store}
  {==}

# The log's lines
# ---------------

law status_back:
  for +s: T.Status
  {St.Status.of(St.Status.tag(s)) == s : T.Status}

def status_back(s):
  match s:
    case T.Open{}:
      {==}
    case T.Underway{}:
      {==}
    case T.Completed{}:
      {==}
    case T.Failed{}:
      {==}
    case T.Cancelled{}:
      {==}

law rec_back:
  for +r: St.Rec
  {St.Rec.of(St.Rec.value(r)) == r : St.Rec}

def rec_back(r):
  match r:
    case St.Rec{i, o, k, a, z, st, d, s}:
      %Equal.sym(T.Status, St.Status.of(St.Status.tag(s)), s, status_back(s)) : {St.Rec{i, o, k, a, z, st, d, _} == St.Rec{i, o, k, a, z, st, d, s} : St.Rec}
      {==}

law org_back:
  for +g: St.Org
  {St.Org.of(St.Org.value(g)) == g : St.Org}

def org_back(g):
  match g:
    case St.Org{i, n, h}:
      {==}

def EV() -> Data:
  Maybe<&2, S.Value(St.Schemas.event())>

law change_back:
  for +e: St.Change
  {St.Change.read(St.Change.write(e)) == Some{e} : MC()}

def change_back(e):
  match e:
    case St.Requested{r}:
      %Equal.sym(EV(), S.decode(St.Schemas.event(), S.encode(St.Schemas.event(), St.Change.value(St.Requested{r}))), Some{St.Change.value(St.Requested{r})},
        PW.roundtrip(St.Schemas.event(), St.Change.value(St.Requested{r}), {==}, PW.within_free(St.Schemas.event(), St.Change.value(St.Requested{r}), {==}))) : {St.Change.found(_) == Some{St.Requested{r}} : MC()}
      %Equal.sym(St.Rec, St.Rec.of(St.Rec.value(r)), r, rec_back(r)) : {Some{St.Requested{_}} == Some{St.Requested{r}} : MC()}
      {==}
    case St.Cancelled{i}:
      %Equal.sym(EV(), S.decode(St.Schemas.event(), S.encode(St.Schemas.event(), St.Change.value(St.Cancelled{i}))), Some{St.Change.value(St.Cancelled{i})},
        PW.roundtrip(St.Schemas.event(), St.Change.value(St.Cancelled{i}), {==}, PW.within_free(St.Schemas.event(), St.Change.value(St.Cancelled{i}), {==}))) : {St.Change.found(_) == Some{St.Cancelled{i}} : MC()}
      {==}
    case St.Organized{g}:
      %Equal.sym(EV(), S.decode(St.Schemas.event(), S.encode(St.Schemas.event(), St.Change.value(St.Organized{g}))), Some{St.Change.value(St.Organized{g})},
        PW.roundtrip(St.Schemas.event(), St.Change.value(St.Organized{g}), {==}, PW.within_free(St.Schemas.event(), St.Change.value(St.Organized{g}), {==}))) : {St.Change.found(_) == Some{St.Organized{g}} : MC()}
      %Equal.sym(St.Org, St.Org.of(St.Org.value(g)), g, org_back(g)) : {Some{St.Organized{_}} == Some{St.Organized{g}} : MC()}
      {==}
    case St.Rekeyed{g}:
      %Equal.sym(EV(), S.decode(St.Schemas.event(), S.encode(St.Schemas.event(), St.Change.value(St.Rekeyed{g}))), Some{St.Change.value(St.Rekeyed{g})},
        PW.roundtrip(St.Schemas.event(), St.Change.value(St.Rekeyed{g}), {==}, PW.within_free(St.Schemas.event(), St.Change.value(St.Rekeyed{g}), {==}))) : {St.Change.found(_) == Some{St.Rekeyed{g}} : MC()}
      %Equal.sym(St.Org, St.Org.of(St.Org.value(g)), g, org_back(g)) : {Some{St.Rekeyed{_}} == Some{St.Rekeyed{g}} : MC()}
      {==}
    case St.Revoked{i}:
      %Equal.sym(EV(), S.decode(St.Schemas.event(), S.encode(St.Schemas.event(), St.Change.value(St.Revoked{i}))), Some{St.Change.value(St.Revoked{i})},
        PW.roundtrip(St.Schemas.event(), St.Change.value(St.Revoked{i}), {==}, PW.within_free(St.Schemas.event(), St.Change.value(St.Revoked{i}), {==}))) : {St.Change.found(_) == Some{St.Revoked{i}} : MC()}
      {==}

# Handlers
# --------

law matches_self:
  for +d: St.Draft
  for +i: String
  for +s: T.Status
  {St.Draft.matches(d, St.Rec.with(St.Rec.new(i, d), s)) == True{} : Bool}

def matches_self(d, i, s):
  match d:
    case St.Draft{o, k, a, z, st, due}:
      L.and_i(J.Text.same(a, a), Bool.and(J.Text.same(z, z), Bool.and(J.Text.same(S.Tag.name(St.Enums.states(), st), S.Tag.name(St.Enums.states(), st)), J.Text.same(due, due))), PW.same_refl(a),
        L.and_i(J.Text.same(z, z), Bool.and(J.Text.same(S.Tag.name(St.Enums.states(), st), S.Tag.name(St.Enums.states(), st)), J.Text.same(due, due)), PW.same_refl(z),
          L.and_i(J.Text.same(S.Tag.name(St.Enums.states(), st), S.Tag.name(St.Enums.states(), st)), J.Text.same(due, due), PW.same_refl(S.Tag.name(St.Enums.states(), st)), PW.same_refl(due))))

law address_differs:
  for +o: String
  for +k: String
  for +a: String
  for +z: String
  for +st: St.StateTag()
  for +due: String
  for +i: String
  for +o2: String
  for +k2: String
  for +a2: String
  for +z2: String
  for +st2: St.StateTag()
  for +d2: String
  for +s: T.Status
  for +e: {J.Text.same(a, a2) == False{} : Bool}
  {St.Draft.matches(St.Draft{o, k, a, z, st, due}, St.Rec{i, o2, k2, a2, z2, st2, d2, s}) == False{} : Bool}

def address_differs(o, k, a, z, st, due, i, o2, k2, a2, z2, st2, d2, s, e):
  %Equal.sym(Bool, J.Text.same(a, a2), False{}, e) : {Bool.and(_, Bool.and(J.Text.same(z, z2), Bool.and(J.Text.same(S.Tag.name(St.Enums.states(), st), S.Tag.name(St.Enums.states(), st2)), J.Text.same(due, d2)))) == False{} : Bool}
  {==}

law repeat_matching_answers_200:
  for +d: St.Draft
  for +r: St.Rec
  for +id: String
  for +m: {St.Draft.matches(d, r) == True{} : Bool}
  {A.Op.status(A.Create{d, Some{r}, id}) == 200n : Nat}

def repeat_matching_answers_200(d, r, id, m):
  %Equal.sym(Bool, St.Draft.matches(d, r), True{}, m) : {A.Reply.status(A.Route.answers(A.Endpoint.route(A.ECreate{})), A.Create.again(_, r)) == 200n : Nat}
  {==}

law repeat_matching_answers_the_record:
  for +d: St.Draft
  for +r: St.Rec
  for +id: String
  for +m: {St.Draft.matches(d, r) == True{} : Bool}
  {A.Reply.body(A.Route.answers(A.Op.route(A.Create{d, Some{r}, id})), A.Api.run(A.Create{d, Some{r}, id})) == S.encode(St.Schemas.appraisal(), St.Rec.value(r)) : J.Json}

def repeat_matching_answers_the_record(d, r, id, m):
  %Equal.sym(Bool, St.Draft.matches(d, r), True{}, m) : {A.Reply.body(A.Route.answers(A.Endpoint.route(A.ECreate{})), A.Create.again(_, r)) == S.encode(St.Schemas.appraisal(), St.Rec.value(r)) : J.Json}
  {==}

law repeat_other_answers_422:
  for +d: St.Draft
  for +r: St.Rec
  for +id: String
  for +m: {St.Draft.matches(d, r) == False{} : Bool}
  {A.Op.status(A.Create{d, Some{r}, id}) == 422n : Nat}

def repeat_other_answers_422(d, r, id, m):
  %Equal.sym(Bool, St.Draft.matches(d, r), False{}, m) : {A.Reply.status(A.Route.answers(A.Endpoint.route(A.ECreate{})), A.Create.again(_, r)) == 422n : Nat}
  {==}

# Blank and control characters
# ----------------------------

def MP() -> Data:
  Maybe<&2, St.Problem>

law spaces_trim_start:
  for +n: Nat
  {String.trim_start(String.repeat(" ", n)) == SNil{} : String}

def spaces_trim_start(n):
  match n:
    case 0n:
      {==}
    case 1n+m:
      spaces_trim_start(m)

law spaces_unfilled:
  for +n: Nat
  {St.Text.filled(String.repeat(" ", n)) == False{} : Bool}

def spaces_unfilled(n):
  %Equal.sym(String, String.trim_start(String.repeat(" ", n)), SNil{}, spaces_trim_start(n)) : {Nat.is_lt(0n, String.length(String.trim_end(_))) == False{} : Bool}
  {==}

law or_true:
  for +a: Bool
  for -b: Bool
  for e: {b == True{} : Bool}
  {Bool.or(a, b) == True{} : Bool}

def or_true(a, b, e):
  match a:
    case True{}:
      {==}
    case False{}:
      e

law or_first:
  for +a: Bool
  for -x: Bool
  for e: {a == True{} : Bool}
  {Bool.or(a, x) == True{} : Bool}

def or_first(a, x, e):
  match a:
    case True{}:
      {==}
    case False{}:
      L.never({Bool.or(False{}, x) == True{} : Bool}, e)

law control_found:
  for +p: String
  for +c: Char
  for +q: String
  for e: {Bool.or(Nat.is_lt(U32.to_nat(Char.to_u32(c)), 32n), Bool.and(Nat.is_le(127n, U32.to_nat(Char.to_u32(c))), Nat.is_le(U32.to_nat(Char.to_u32(c)), 159n))) == True{} : Bool}
  {St.Text.control(String.append(p, SCon{c, q})) == True{} : Bool}

def control_found(p, c, q, e):
  match p:
    case SNil{}:
      or_first(Bool.or(Nat.is_lt(J.Text.code(c), 32n), Bool.and(Nat.is_le(127n, J.Text.code(c)), Nat.is_le(J.Text.code(c), 159n))), St.Text.control(q), e)
    case SCon{+h, t}:
      or_true(Bool.or(Nat.is_lt(J.Text.code(h), 32n), Bool.and(Nat.is_le(127n, J.Text.code(h)), Nat.is_le(J.Text.code(h), 159n))), St.Text.control(String.append(t, SCon{c, q})), control_found(t, c, q, e))

# A rule that fails is a problem, and a problem found later stays one.
law first_fails:
  for +b: Bool
  for +c: String
  for +t: String
  for +r: MP()
  for e: {b == False{} : Bool}
  {Maybe.is_some(&2, St.Problem, St.Draft.first(b, c, t, r)) == True{} : Bool}

def first_fails(b, c, t, r, e):
  %Equal.sym(Bool, b, False{}, e) : {Maybe.is_some(&2, St.Problem, St.Draft.first(_, c, t, r)) == True{} : Bool}
  {==}

law first_keeps:
  for +b: Bool
  for +c: String
  for +t: String
  for +r: MP()
  for e: {Maybe.is_some(&2, St.Problem, r) == True{} : Bool}
  {Maybe.is_some(&2, St.Problem, St.Draft.first(b, c, t, r)) == True{} : Bool}

def first_keeps(b, c, t, r, e):
  match b:
    case True{}:
      e
    case False{}:
      {==}

# The three rules a key, an address and a name each keep: a length, not
# blank, and no control characters.
def Checks(+s: String, lo: Nat, hi: Nat, +c: String, t1: String, t2: String, t3: String, r: MP()) -> MP():
  St.Draft.first(St.Text.sized(s, lo, hi), c, t1, St.Draft.first(St.Text.filled(s), c, t2, St.Draft.first(Bool.not(St.Text.control(s)), c, t3, r)))

law checks_blank:
  for +s: String
  for +lo: Nat
  for +hi: Nat
  for +c: String
  for +t1: String
  for +t2: String
  for +t3: String
  for +r: MP()
  for e: {St.Text.filled(s) == False{} : Bool}
  {Maybe.is_some(&2, St.Problem, Checks(s, lo, hi, c, t1, t2, t3, r)) == True{} : Bool}

def checks_blank(s, lo, hi, c, t1, t2, t3, r, e):
  first_keeps(St.Text.sized(s, lo, hi), c, t1, St.Draft.first(St.Text.filled(s), c, t2, St.Draft.first(Bool.not(St.Text.control(s)), c, t3, r)),
    first_fails(St.Text.filled(s), c, t2, St.Draft.first(Bool.not(St.Text.control(s)), c, t3, r), e))

law checks_control:
  for +s: String
  for +lo: Nat
  for +hi: Nat
  for +c: String
  for +t1: String
  for +t2: String
  for +t3: String
  for +r: MP()
  for e: {St.Text.control(s) == True{} : Bool}
  {Maybe.is_some(&2, St.Problem, Checks(s, lo, hi, c, t1, t2, t3, r)) == True{} : Bool}

def checks_control(s, lo, hi, c, t1, t2, t3, r, e):
  first_keeps(St.Text.sized(s, lo, hi), c, t1, St.Draft.first(St.Text.filled(s), c, t2, St.Draft.first(Bool.not(St.Text.control(s)), c, t3, r)),
    first_keeps(St.Text.filled(s), c, t2, St.Draft.first(Bool.not(St.Text.control(s)), c, t3, r),
      first_fails(Bool.not(St.Text.control(s)), c, t3, r, Equal.cong(Bool, Bool, x => Bool.not(x), St.Text.control(s), True{}, e))))

law checks_keep:
  for +s: String
  for +lo: Nat
  for +hi: Nat
  for +c: String
  for +t1: String
  for +t2: String
  for +t3: String
  for +r: MP()
  for e: {Maybe.is_some(&2, St.Problem, r) == True{} : Bool}
  {Maybe.is_some(&2, St.Problem, Checks(s, lo, hi, c, t1, t2, t3, r)) == True{} : Bool}

def checks_keep(s, lo, hi, c, t1, t2, t3, r, e):
  first_keeps(St.Text.sized(s, lo, hi), c, t1, St.Draft.first(St.Text.filled(s), c, t2, St.Draft.first(Bool.not(St.Text.control(s)), c, t3, r)),
    first_keeps(St.Text.filled(s), c, t2, St.Draft.first(Bool.not(St.Text.control(s)), c, t3, r),
      first_keeps(Bool.not(St.Text.control(s)), c, t3, r, e)))

# What follows the address in Draft.problem, and the address's rules.
def Dated(z: String, due: String) -> MP():
  St.Draft.first(St.Text.digits(5n, z), "invalid_zip", "zip must be 5 digits",
    St.Draft.first(St.Date.ok(due), "invalid_due", "due must be a date, YYYY-MM-DD", None{}))

def Addressed(+a: String, z: String, due: String) -> MP():
  Checks(a, 1n, 200n, "invalid_address", "address must be 1 to 200 characters", "address must not be blank", "address must not hold control characters", Dated(z, due))

law blank_key:
  for +o: String
  for +n: Nat
  for +a: String
  for +z: String
  for +st: St.StateTag()
  for +due: String
  {Maybe.is_some(&2, St.Problem, St.Draft.problem(St.Draft{o, String.repeat(" ", n), a, z, st, due})) == True{} : Bool}

def blank_key(o, n, a, z, st, due):
  checks_blank(String.repeat(" ", n), 1n, 64n, "invalid_key", "key must be 1 to 64 characters", "key must not be blank", "key must not hold control characters", Addressed(a, z, due), spaces_unfilled(n))

law control_key:
  for +o: String
  for +p: String
  for +c: Char
  for +q: String
  for +a: String
  for +z: String
  for +st: St.StateTag()
  for +due: String
  for e: {Bool.or(Nat.is_lt(U32.to_nat(Char.to_u32(c)), 32n), Bool.and(Nat.is_le(127n, U32.to_nat(Char.to_u32(c))), Nat.is_le(U32.to_nat(Char.to_u32(c)), 159n))) == True{} : Bool}
  {Maybe.is_some(&2, St.Problem, St.Draft.problem(St.Draft{o, String.append(p, SCon{c, q}), a, z, st, due})) == True{} : Bool}

def control_key(o, p, c, q, a, z, st, due, e):
  checks_control(String.append(p, SCon{c, q}), 1n, 64n, "invalid_key", "key must be 1 to 64 characters", "key must not be blank", "key must not hold control characters", Addressed(a, z, due), control_found(p, c, q, e))

law blank_address:
  for +o: String
  for +k: String
  for +n: Nat
  for +z: String
  for +st: St.StateTag()
  for +due: String
  {Maybe.is_some(&2, St.Problem, St.Draft.problem(St.Draft{o, k, String.repeat(" ", n), z, st, due})) == True{} : Bool}

def blank_address(o, k, n, z, st, due):
  checks_keep(k, 1n, 64n, "invalid_key", "key must be 1 to 64 characters", "key must not be blank", "key must not hold control characters", Addressed(String.repeat(" ", n), z, due),
    checks_blank(String.repeat(" ", n), 1n, 200n, "invalid_address", "address must be 1 to 200 characters", "address must not be blank", "address must not hold control characters", Dated(z, due), spaces_unfilled(n)))

law control_address:
  for +o: String
  for +k: String
  for +p: String
  for +c: Char
  for +q: String
  for +z: String
  for +st: St.StateTag()
  for +due: String
  for e: {Bool.or(Nat.is_lt(U32.to_nat(Char.to_u32(c)), 32n), Bool.and(Nat.is_le(127n, U32.to_nat(Char.to_u32(c))), Nat.is_le(U32.to_nat(Char.to_u32(c)), 159n))) == True{} : Bool}
  {Maybe.is_some(&2, St.Problem, St.Draft.problem(St.Draft{o, k, String.append(p, SCon{c, q}), z, st, due})) == True{} : Bool}

def control_address(o, k, p, c, q, z, st, due, e):
  checks_keep(k, 1n, 64n, "invalid_key", "key must be 1 to 64 characters", "key must not be blank", "key must not hold control characters", Addressed(String.append(p, SCon{c, q}), z, due),
    checks_control(String.append(p, SCon{c, q}), 1n, 200n, "invalid_address", "address must be 1 to 200 characters", "address must not be blank", "address must not hold control characters", Dated(z, due), control_found(p, c, q, e)))

law blank_name:
  for +n: Nat
  {Maybe.is_some(&2, St.Problem, St.Org.problem(String.repeat(" ", n))) == True{} : Bool}

def blank_name(n):
  checks_blank(String.repeat(" ", n), 1n, 100n, "invalid_name", "name must be 1 to 100 characters", "name must not be blank", "name must not hold control characters", None{}, spaces_unfilled(n))

law control_name:
  for +p: String
  for +c: Char
  for +q: String
  for e: {Bool.or(Nat.is_lt(U32.to_nat(Char.to_u32(c)), 32n), Bool.and(Nat.is_le(127n, U32.to_nat(Char.to_u32(c))), Nat.is_le(U32.to_nat(Char.to_u32(c)), 159n))) == True{} : Bool}
  {Maybe.is_some(&2, St.Problem, St.Org.problem(String.append(p, SCon{c, q}))) == True{} : Bool}

def control_name(p, c, q, e):
  checks_control(String.append(p, SCon{c, q}), 1n, 100n, "invalid_name", "name must be 1 to 100 characters", "name must not be blank", "name must not hold control characters", None{}, control_found(p, c, q, e))

law broken_request_changes_nothing:
  for +d: St.Draft
  for +id: String
  for +c: String
  for +t: String
  for +p: {St.Draft.problem(d) == Some{St.Problem{c, t}} : Maybe<&2, St.Problem>}
  {A.Api.change(A.Create{d, None{}, id}) == None{} : MC()}

def broken_request_changes_nothing(d, id, c, t, p):
  %Equal.sym(Maybe<&2, St.Problem>, St.Draft.problem(d), Some{St.Problem{c, t}}, p) : {A.Create.made(_, d, id) == None{} : MC()}
  {==}

law broken_request_is_refused:
  for +d: St.Draft
  for +id: String
  for +c: String
  for +t: String
  for +p: {St.Draft.problem(d) == Some{St.Problem{c, t}} : Maybe<&2, St.Problem>}
  {A.Op.status(A.Create{d, None{}, id}) == 422n : Nat}

def broken_request_is_refused(d, id, c, t, p):
  %Equal.sym(Maybe<&2, St.Problem>, St.Draft.problem(d), Some{St.Problem{c, t}}, p) : {A.Reply.status(A.Route.answers(A.Endpoint.route(A.ECreate{})), A.Create.fresh(_, d, id)) == 422n : Nat}
  {==}

law good_request_is_logged:
  for +d: St.Draft
  for +id: String
  for +p: {St.Draft.problem(d) == None{} : Maybe<&2, St.Problem>}
  {A.Api.change(A.Create{d, None{}, id}) == Some{St.Requested{St.Rec.new(id, d)}} : MC()}

def good_request_is_logged(d, id, p):
  %Equal.sym(Maybe<&2, St.Problem>, St.Draft.problem(d), None{}, p) : {A.Create.made(_, d, id) == Some{St.Requested{St.Rec.new(id, d)}} : MC()}
  {==}

law good_request_is_created:
  for +d: St.Draft
  for +id: String
  for +p: {St.Draft.problem(d) == None{} : Maybe<&2, St.Problem>}
  {A.Op.status(A.Create{d, None{}, id}) == 201n : Nat}

def good_request_is_created(d, id, p):
  %Equal.sym(Maybe<&2, St.Problem>, St.Draft.problem(d), None{}, p) : {A.Reply.status(A.Route.answers(A.Endpoint.route(A.ECreate{})), A.Create.fresh(_, d, id)) == 201n : Nat}
  {==}

law locked_appraisal_isnt_cancelled:
  for +r: St.Rec
  for +e: {Life.Status.locked(St.Rec.status(r)) == True{} : Bool}
  {A.Api.change(A.Cancel{Some{r}}) == None{} : MC()}

def locked_appraisal_isnt_cancelled(r, e):
  match r:
    case St.Rec{i, o, k, a, z, st, d, s}:
      match s:
        case T.Underway{}:
          {==}
        case T.Completed{}:
          {==}
        case T.Open{}:
          L.never({A.Api.change(A.Cancel{Some{St.Rec{i, o, k, a, z, st, d, T.Open{}}}}) == None{} : MC()}, e)
        case T.Failed{}:
          L.never({A.Api.change(A.Cancel{Some{St.Rec{i, o, k, a, z, st, d, T.Failed{}}}}) == None{} : MC()}, e)
        case T.Cancelled{}:
          L.never({A.Api.change(A.Cancel{Some{St.Rec{i, o, k, a, z, st, d, T.Cancelled{}}}}) == None{} : MC()}, e)

law locked_appraisal_is_a_conflict:
  for +r: St.Rec
  for +e: {Life.Status.locked(St.Rec.status(r)) == True{} : Bool}
  {A.Op.status(A.Cancel{Some{r}}) == 409n : Nat}

def locked_appraisal_is_a_conflict(r, e):
  match r:
    case St.Rec{i, o, k, a, z, st, d, s}:
      match s:
        case T.Underway{}:
          {==}
        case T.Completed{}:
          {==}
        case T.Open{}:
          L.never({A.Op.status(A.Cancel{Some{St.Rec{i, o, k, a, z, st, d, T.Open{}}}}) == 409n : Nat}, e)
        case T.Failed{}:
          L.never({A.Op.status(A.Cancel{Some{St.Rec{i, o, k, a, z, st, d, T.Failed{}}}}) == 409n : Nat}, e)
        case T.Cancelled{}:
          L.never({A.Op.status(A.Cancel{Some{St.Rec{i, o, k, a, z, st, d, T.Cancelled{}}}}) == 409n : Nat}, e)
