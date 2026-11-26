import Base
import ../web/json.bend as J
import ../web/schema.bend as S
import ../web/store.bend as St
import ../web/api.bend as A
import ./logic.bend as L
import ./web.bend as PW

# Proofs about API keys, the gate and tenant isolation. LAWS.bend states the
# rules; these prove them.

def MS() -> Data:
  Maybe<&2, St.Rec>

# Telling values apart
# --------------------

def is_pass(g: A.Gate) -> Bool:
  match g:
    case A.Pass{o}:
      True{}
    case A.Deny{s, c}:
      False{}

# The caller a gate passed, as the dealer it passed.
def passed(g: A.Gate) -> A.Who:
  match g:
    case A.Pass{o}:
      A.Dealer{o}
    case A.Deny{s, c}:
      A.Nobody{}

def is_dealer(w: A.Who) -> Bool:
  match w:
    case A.Dealer{o}:
      True{}
    case other:
      False{}

def is_admin(w: A.Who) -> Bool:
  match w:
    case A.Admin{}:
      True{}
    case other:
      False{}

def dealer_of(w: A.Who) -> String:
  match w:
    case A.Dealer{o}:
      o
    case other:
      ""

def org_of(m: Maybe<&2, St.Rec>) -> String:
  match m:
    case Some{r}:
      St.Rec.org(r)
    case None{}:
      ""

def is_handle(x: A.Resolved) -> Bool:
  match x:
    case A.Handle{op}:
      True{}
    case A.Refuse{s, c}:
      False{}

def op_found(op: A.Op) -> Maybe<&2, St.Rec>:
  match op:
    case A.Fetch{m}:
      m
    case A.Cancel{m}:
      m
    case A.Create{d, m, i}:
      m
    case other:
      None{}

# The record a resolved request carries: the one Fetch or Cancel found, or
# the one Create found under its key.
def found(x: A.Resolved) -> Maybe<&2, St.Rec>:
  match x:
    case A.Handle{op}:
      op_found(op)
    case A.Refuse{s, c}:
      None{}

def op_draft(op: A.Op, d: St.Draft) -> St.Draft:
  match op:
    case A.Create{x, m, i}:
      x
    case other:
      d

def drafted(x: A.Resolved, d: St.Draft) -> St.Draft:
  match x:
    case A.Handle{op}:
      op_draft(op, d)
    case A.Refuse{s, c}:
      d

# Bools
# -----

law or_left:
  for +a: Bool
  for -b: Bool
  for e: {a == True{} : Bool}
  {Bool.or(a, b) == True{} : Bool}

def or_left(a, b, e):
  match a:
    case True{}:
      {==}
    case False{}:
      L.never({Bool.or(False{}, b) == True{} : Bool}, e)

law or_right:
  for +a: Bool
  for -b: Bool
  for e: {b == True{} : Bool}
  {Bool.or(a, b) == True{} : Bool}

def or_right(a, b, e):
  match a:
    case True{}:
      {==}
    case False{}:
      e

law same_back:
  for +a: String
  for +b: String
  for q: {b == a : String}
  {J.Text.same(a, b) == True{} : Bool}

def same_back(a, b, q):
  %q : {J.Text.same(_, b) == True{} : Bool}
  PW.same_refl(b)

# The gate
# --------

law dealers_pass:
  for +w: A.Who
  for +o: String
  for e: {A.Api.gate(A.Dealers{}, w) == A.Pass{o} : A.Gate}
  {w == A.Dealer{o} : A.Who}

def dealers_pass(w, o, e):
  match w:
    case A.Nobody{}:
      L.never({A.Nobody{} == A.Dealer{o} : A.Who}, Equal.cong(A.Gate, Bool, g => is_pass(g), A.Deny{A.Unauthorized{}, "unauthorized"}, A.Pass{o}, e))
    case A.Admin{}:
      L.never({A.Admin{} == A.Dealer{o} : A.Who}, Equal.cong(A.Gate, Bool, g => is_pass(g), A.Deny{A.Forbidden{}, "forbidden"}, A.Pass{o}, e))
    case A.Dealer{x}:
      Equal.cong(A.Gate, A.Who, g => passed(g), A.Pass{x}, A.Pass{o}, e)

law admins_pass:
  for +w: A.Who
  for +o: String
  for e: {A.Api.gate(A.Admins{}, w) == A.Pass{o} : A.Gate}
  {w == A.Admin{} : A.Who}

def admins_pass(w, o, e):
  match w:
    case A.Nobody{}:
      L.never({A.Nobody{} == A.Admin{} : A.Who}, Equal.cong(A.Gate, Bool, g => is_pass(g), A.Deny{A.Unauthorized{}, "unauthorized"}, A.Pass{o}, e))
    case A.Admin{}:
      {==}
    case A.Dealer{x}:
      L.never({A.Dealer{x} == A.Admin{} : A.Who}, Equal.cong(A.Gate, Bool, g => is_pass(g), A.Deny{A.Forbidden{}, "forbidden"}, A.Pass{o}, e))

# Who a key belongs to
# --------------------

law dealer_pick:
  for +b: Bool
  for +h: String
  for +g: St.Org
  for +rest: List<&2, St.Org>
  for +o: String
  for eb: {J.Text.same(h, St.Org.hash(g)) == b : Bool}
  for e: {A.Api.dealer(St.Orgs.pick(b, g, St.Orgs.by_hash(h, rest))) == A.Dealer{o} : A.Who}
  for ih: {A.Api.dealer(St.Orgs.by_hash(h, rest)) == A.Dealer{o} : A.Who} -> {St.Orgs.holds(o, h, rest) == True{} : Bool}
  {St.Orgs.holds(o, h, g <> rest) == True{} : Bool}

def dealer_pick(b, h, g, rest, o, eb, e, ih):
  match b:
    case True{}:
      or_left(Bool.and(J.Text.same(o, St.Org.id(g)), J.Text.same(h, St.Org.hash(g))), St.Orgs.holds(o, h, rest),
        L.and_i(J.Text.same(o, St.Org.id(g)), J.Text.same(h, St.Org.hash(g)),
          same_back(o, St.Org.id(g), Equal.cong(A.Who, String, w => dealer_of(w), A.Dealer{St.Org.id(g)}, A.Dealer{o}, e)), eb))
    case False{}:
      or_right(Bool.and(J.Text.same(o, St.Org.id(g)), J.Text.same(h, St.Org.hash(g))), St.Orgs.holds(o, h, rest), ih(e))

law dealer_holds:
  for +h: String
  for +gs: List<&2, St.Org>
  for +o: String
  for e: {A.Api.dealer(St.Orgs.by_hash(h, gs)) == A.Dealer{o} : A.Who}
  {St.Orgs.holds(o, h, gs) == True{} : Bool}

def dealer_holds(h, gs, o, e):
  match gs:
    case Nil{}:
      L.never({St.Orgs.holds(o, h, Nil{}) == True{} : Bool}, Equal.cong(A.Who, Bool, w => is_dealer(w), A.Nobody{}, A.Dealer{o}, e))
    case Con{g, rest}:
      dealer_pick(J.Text.same(h, St.Org.hash(g)), h, g, rest, o, {==}, e, x => dealer_holds(h, rest, o, x))

law known_pick:
  for +b: Bool
  for +h: String
  for +gs: List<&2, St.Org>
  for +o: String
  for e: {A.Api.known.pick(b, h, gs) == A.Dealer{o} : A.Who}
  {St.Orgs.holds(o, h, gs) == True{} : Bool}

def known_pick(b, h, gs, o, e):
  match b:
    case True{}:
      L.never({St.Orgs.holds(o, h, gs) == True{} : Bool}, Equal.cong(A.Who, Bool, w => is_dealer(w), A.Admin{}, A.Dealer{o}, e))
    case False{}:
      dealer_holds(h, gs, o, e)

law known_dealer:
  for +h: String
  for +admin: Maybe<&2, String>
  for +gs: List<&2, St.Org>
  for +o: String
  for e: {A.Api.known(h, admin, gs) == A.Dealer{o} : A.Who}
  {St.Orgs.holds(o, h, gs) == True{} : Bool}

def known_dealer(h, admin, gs, o, e):
  match admin:
    case None{}:
      dealer_holds(h, gs, o, e)
    case Some{a}:
      known_pick(J.Text.same(h, a), h, gs, o, e)

law dealer_not_admin:
  for +m: Maybe<&2, St.Org>
  for e: {A.Api.dealer(m) == A.Admin{} : A.Who}
  Empty

def dealer_not_admin(m, e):
  match m:
    case None{}:
      L.ff(Equal.cong(A.Who, Bool, w => is_admin(w), A.Nobody{}, A.Admin{}, e))
    case Some{g}:
      L.ff(Equal.cong(A.Who, Bool, w => is_admin(w), A.Dealer{St.Org.id(g)}, A.Admin{}, e))

# Laws about keys speak of the hash h of the key a request brings, which
# Api.who takes with Sha.text. The checker can't unfold Sha.text on a key it
# doesn't know, so they stop at Api.known.
law no_admin:
  for +h: String
  for +gs: List<&2, St.Org>
  for e: {A.Api.known(h, None{}, gs) == A.Admin{} : A.Who}
  Empty

def no_admin(h, gs, e):
  dealer_not_admin(St.Orgs.by_hash(h, gs), e)

law new_key_signs_in:
  for +h: String
  for +i: String
  for +n: String
  for +gs: List<&2, St.Org>
  {A.Api.known(h, None{}, St.Org{i, n, h} <> gs) == A.Dealer{i} : A.Who}

def new_key_signs_in(h, i, n, gs):
  %Equal.sym(Bool, J.Text.same(h, h), True{}, PW.same_refl(h)) : {A.Api.dealer(St.Orgs.pick(_, St.Org{i, n, h}, St.Orgs.by_hash(h, gs))) == A.Dealer{i} : A.Who}
  {==}

law new_key_beside_admin:
  for +h: String
  for +a: String
  for +i: String
  for +n: String
  for +gs: List<&2, St.Org>
  for +e: {J.Text.same(h, a) == False{} : Bool}
  {A.Api.known(h, Some{a}, St.Org{i, n, h} <> gs) == A.Dealer{i} : A.Who}

def new_key_beside_admin(h, a, i, n, gs, e):
  %Equal.sym(Bool, J.Text.same(h, a), False{}, e) : {A.Api.known.pick(_, h, St.Org{i, n, h} <> gs) == A.Dealer{i} : A.Who}
  new_key_signs_in(h, i, n, gs)

# Owned lookups
# -------------

law owned_pick:
  for +b: Bool
  for +o: String
  for +i: String
  for +x: St.Rec
  for +rest: List<&2, St.Rec>
  for +r: St.Rec
  for eb: {Bool.and(J.Text.same(i, St.Rec.id(x)), J.Text.same(o, St.Rec.org(x))) == b : Bool}
  for e: {St.Store.find.pick(b, x, St.Store.owned(o, i, rest)) == Some{r} : MS()}
  for ih: {St.Store.owned(o, i, rest) == Some{r} : MS()} -> {J.Text.same(o, St.Rec.org(r)) == True{} : Bool}
  {J.Text.same(o, St.Rec.org(r)) == True{} : Bool}

def owned_pick(b, o, i, x, rest, r, eb, e, ih):
  match b:
    case True{}:
      %Equal.cong(MS(), String, m => org_of(m), Some{x}, Some{r}, e) : {J.Text.same(o, _) == True{} : Bool}
      L.and_r(J.Text.same(i, St.Rec.id(x)), J.Text.same(o, St.Rec.org(x)), eb)
    case False{}:
      ih(e)

law owned_is_the_callers:
  for +o: String
  for +i: String
  for +rs: List<&2, St.Rec>
  for +r: St.Rec
  for e: {St.Store.owned(o, i, rs) == Some{r} : MS()}
  {J.Text.same(o, St.Rec.org(r)) == True{} : Bool}

def owned_is_the_callers(o, i, rs, r, e):
  match rs:
    case Nil{}:
      L.never({J.Text.same(o, St.Rec.org(r)) == True{} : Bool}, Equal.cong(MS(), Bool, m => Maybe.is_some(&2, St.Rec, m), None{}, Some{r}, e))
    case Con{x, rest}:
      owned_pick(Bool.and(J.Text.same(i, St.Rec.id(x)), J.Text.same(o, St.Rec.org(x))), o, i, x, rest, r, {==}, e, q => owned_is_the_callers(o, i, rest, r, q))

law keyed_pick:
  for +b: Bool
  for +o: String
  for +k: String
  for +x: St.Rec
  for +rest: List<&2, St.Rec>
  for +r: St.Rec
  for eb: {Bool.and(J.Text.same(k, St.Rec.key(x)), J.Text.same(o, St.Rec.org(x))) == b : Bool}
  for e: {St.Store.find.pick(b, x, St.Store.by_key(o, k, rest)) == Some{r} : MS()}
  for ih: {St.Store.by_key(o, k, rest) == Some{r} : MS()} -> {J.Text.same(o, St.Rec.org(r)) == True{} : Bool}
  {J.Text.same(o, St.Rec.org(r)) == True{} : Bool}

def keyed_pick(b, o, k, x, rest, r, eb, e, ih):
  match b:
    case True{}:
      %Equal.cong(MS(), String, m => org_of(m), Some{x}, Some{r}, e) : {J.Text.same(o, _) == True{} : Bool}
      L.and_r(J.Text.same(k, St.Rec.key(x)), J.Text.same(o, St.Rec.org(x)), eb)
    case False{}:
      ih(e)

law keyed_is_the_callers:
  for +o: String
  for +k: String
  for +rs: List<&2, St.Rec>
  for +r: St.Rec
  for e: {St.Store.by_key(o, k, rs) == Some{r} : MS()}
  {J.Text.same(o, St.Rec.org(r)) == True{} : Bool}

def keyed_is_the_callers(o, k, rs, r, e):
  match rs:
    case Nil{}:
      L.never({J.Text.same(o, St.Rec.org(r)) == True{} : Bool}, Equal.cong(MS(), Bool, m => Maybe.is_some(&2, St.Rec, m), None{}, Some{r}, e))
    case Con{x, rest}:
      keyed_pick(Bool.and(J.Text.same(k, St.Rec.key(x)), J.Text.same(o, St.Rec.org(x))), o, k, x, rest, r, {==}, e, q => keyed_is_the_callers(o, k, rest, r, q))

# Resolving requests
# ------------------

law fetch_is_the_callers:
  for +ps: List<&2, String>
  for +body: String
  for +s: St.Store
  for +o: String
  for +seed: List<&2, U32>
  for +r: St.Rec
  for e: {A.Api.resolve(A.EFetch{}, ps, body, s, o, seed) == A.Handle{A.Fetch{Some{r}}} : A.Resolved}
  {J.Text.same(o, St.Rec.org(r)) == True{} : Bool}

def fetch_is_the_callers(ps, body, s, o, seed, r, e):
  owned_is_the_callers(o, A.Path.first(ps), St.Store.recs(s), r,
    Equal.cong(A.Resolved, MS(), x => found(x), A.Handle{A.Fetch{St.Store.owned(o, A.Path.first(ps), St.Store.recs(s))}}, A.Handle{A.Fetch{Some{r}}}, e))

law cancel_is_the_callers:
  for +ps: List<&2, String>
  for +body: String
  for +s: St.Store
  for +o: String
  for +seed: List<&2, U32>
  for +r: St.Rec
  for e: {A.Api.resolve(A.ECancel{}, ps, body, s, o, seed) == A.Handle{A.Cancel{Some{r}}} : A.Resolved}
  {J.Text.same(o, St.Rec.org(r)) == True{} : Bool}

def cancel_is_the_callers(ps, body, s, o, seed, r, e):
  owned_is_the_callers(o, A.Path.first(ps), St.Store.recs(s), r,
    Equal.cong(A.Resolved, MS(), x => found(x), A.Handle{A.Cancel{St.Store.owned(o, A.Path.first(ps), St.Store.recs(s))}}, A.Handle{A.Cancel{Some{r}}}, e))

law create_known:
  for +m: Maybe<&2, St.Draft>
  for +o: String
  for +s: St.Store
  for +d: St.Draft
  for +r: St.Rec
  for +id: String
  for e: {A.Api.create(m, o, s) == A.Handle{A.Create{d, Some{r}, id}} : A.Resolved}
  {J.Text.same(o, St.Rec.org(r)) == True{} : Bool}

def create_known(m, o, s, d, r, id, e):
  match m:
    case None{}:
      L.never({J.Text.same(o, St.Rec.org(r)) == True{} : Bool}, Equal.cong(A.Resolved, Bool, x => is_handle(x), A.Refuse{A.BadRequest{}, "invalid_body"}, A.Handle{A.Create{d, Some{r}, id}}, e))
    case Some{x}:
      keyed_is_the_callers(o, St.Draft.key(x), St.Store.recs(s), r,
        Equal.cong(A.Resolved, MS(), y => found(y), A.Handle{A.Create{x, St.Store.by_key(o, St.Draft.key(x), St.Store.recs(s)), St.Store.next(s)}}, A.Handle{A.Create{d, Some{r}, id}}, e))

law draft_org:
  for +o: String
  for +v: S.Value(St.Schemas.draft())
  {St.Draft.org(St.Draft.of(o, v)) == o : String}

def draft_org(o, v):
  match v:
    case (k, r1):
      match r1:
        case (a, r2):
          match r2:
            case (z, r3):
              match r3:
                case (st, r4):
                  match r4:
                    case (d, u):
                      {==}

law draft_of_is_the_callers:
  for +o: String
  for +mv: Maybe<&2, S.Value(St.Schemas.draft())>
  for +d: St.Draft
  for e: {A.Api.draft.of(o, mv) == Some{d} : Maybe<&2, St.Draft>}
  {St.Draft.org(d) == o : String}

def draft_of_is_the_callers(o, mv, d, e):
  match mv:
    case None{}:
      L.never({St.Draft.org(d) == o : String}, Equal.cong(Maybe<&2, St.Draft>, Bool, m => Maybe.is_some(&2, St.Draft, m), None{}, Some{d}, e))
    case Some{v}:
      %Equal.cong(Maybe<&2, St.Draft>, St.Draft, m => Maybe.default(&2, St.Draft, m, d), Some{St.Draft.of(o, v)}, Some{d}, e) : {St.Draft.org(_) == o : String}
      draft_org(o, v)

law draft_json_is_the_callers:
  for +o: String
  for +mj: Maybe<&2, J.Json>
  for +d: St.Draft
  for e: {A.Api.draft.json(o, mj) == Some{d} : Maybe<&2, St.Draft>}
  {St.Draft.org(d) == o : String}

def draft_json_is_the_callers(o, mj, d, e):
  match mj:
    case None{}:
      L.never({St.Draft.org(d) == o : String}, Equal.cong(Maybe<&2, St.Draft>, Bool, m => Maybe.is_some(&2, St.Draft, m), None{}, Some{d}, e))
    case Some{j}:
      draft_of_is_the_callers(o, S.decode(St.Schemas.draft(), j), d, e)

law create_draft:
  for +m: Maybe<&2, St.Draft>
  for +o: String
  for +s: St.Store
  for +d: St.Draft
  for +k: Maybe<&2, St.Rec>
  for +id: String
  for e: {A.Api.create(m, o, s) == A.Handle{A.Create{d, k, id}} : A.Resolved}
  {m == Some{d} : Maybe<&2, St.Draft>}

def create_draft(m, o, s, d, k, id, e):
  match m:
    case None{}:
      L.never({None{} == Some{d} : Maybe<&2, St.Draft>}, Equal.cong(A.Resolved, Bool, x => is_handle(x), A.Refuse{A.BadRequest{}, "invalid_body"}, A.Handle{A.Create{d, k, id}}, e))
    case Some{x}:
      %Equal.cong(A.Resolved, St.Draft, y => drafted(y, d), A.Handle{A.Create{x, St.Store.by_key(o, St.Draft.key(x), St.Store.recs(s)), St.Store.next(s)}}, A.Handle{A.Create{d, k, id}}, e) : {Some{x} == Some{_} : Maybe<&2, St.Draft>}
      {==}

law create_is_the_callers:
  for +ps: List<&2, String>
  for +body: String
  for +s: St.Store
  for +o: String
  for +seed: List<&2, U32>
  for +d: St.Draft
  for +k: Maybe<&2, St.Rec>
  for +id: String
  for e: {A.Api.resolve(A.ECreate{}, ps, body, s, o, seed) == A.Handle{A.Create{d, k, id}} : A.Resolved}
  {St.Draft.org(d) == o : String}

def create_is_the_callers(ps, body, s, o, seed, d, k, id, e):
  draft_json_is_the_callers(o, A.Api.json(body), d, create_draft(A.Api.draft(o, body), o, s, d, k, id, e))

# Adding organizations
# --------------------

def MC() -> Data:
  Maybe<&2, St.Change>

law bad_name_changes_nothing:
  for +n: String
  for +i: String
  for +k: String
  for +h: String
  for +c: String
  for +t: String
  for +p: {St.Org.problem(n) == Some{St.Problem{c, t}} : Maybe<&2, St.Problem>}
  {A.Api.change(A.Organize{n, i, k, h}) == None{} : MC()}

def bad_name_changes_nothing(n, i, k, h, c, t, p):
  %Equal.sym(Maybe<&2, St.Problem>, St.Org.problem(n), Some{St.Problem{c, t}}, p) : {A.Organize.made(_, n, i, h) == None{} : MC()}
  {==}

law bad_name_is_refused:
  for +n: String
  for +i: String
  for +k: String
  for +h: String
  for +c: String
  for +t: String
  for +p: {St.Org.problem(n) == Some{St.Problem{c, t}} : Maybe<&2, St.Problem>}
  {A.Op.status(A.Organize{n, i, k, h}) == 422n : Nat}

def bad_name_is_refused(n, i, k, h, c, t, p):
  %Equal.sym(Maybe<&2, St.Problem>, St.Org.problem(n), Some{St.Problem{c, t}}, p) : {A.Reply.status(A.Route.answers(A.Endpoint.route(A.EOrganize{})), A.Organize.reply(_, n, i, k)) == 422n : Nat}
  {==}

law good_name_is_logged:
  for +n: String
  for +i: String
  for +k: String
  for +h: String
  for +p: {St.Org.problem(n) == None{} : Maybe<&2, St.Problem>}
  {A.Api.change(A.Organize{n, i, k, h}) == Some{St.Organized{St.Org{i, n, h}}} : MC()}

def good_name_is_logged(n, i, k, h, p):
  %Equal.sym(Maybe<&2, St.Problem>, St.Org.problem(n), None{}, p) : {A.Organize.made(_, n, i, h) == Some{St.Organized{St.Org{i, n, h}}} : MC()}
  {==}

law good_name_is_created:
  for +n: String
  for +i: String
  for +k: String
  for +h: String
  for +p: {St.Org.problem(n) == None{} : Maybe<&2, St.Problem>}
  {A.Op.status(A.Organize{n, i, k, h}) == 201n : Nat}

def good_name_is_created(n, i, k, h, p):
  %Equal.sym(Maybe<&2, St.Problem>, St.Org.problem(n), None{}, p) : {A.Reply.status(A.Route.answers(A.Endpoint.route(A.EOrganize{})), A.Organize.reply(_, n, i, k)) == 201n : Nat}
  {==}

law good_name_answers_the_key:
  for +n: String
  for +i: String
  for +k: String
  for +h: String
  for +p: {St.Org.problem(n) == None{} : Maybe<&2, St.Problem>}
  {A.Reply.body(A.Route.answers(A.Op.route(A.Organize{n, i, k, h})), A.Api.run(A.Organize{n, i, k, h})) == S.encode(St.Schemas.org.key(), (i, (n, (k, Unit{})))) : J.Json}

def good_name_answers_the_key(n, i, k, h, p):
  %Equal.sym(Maybe<&2, St.Problem>, St.Org.problem(n), None{}, p) : {A.Reply.body(A.Route.answers(A.Endpoint.route(A.EOrganize{})), A.Organize.reply(_, n, i, k)) == S.encode(St.Schemas.org.key(), (i, (n, (k, Unit{})))) : J.Json}
  {==}

