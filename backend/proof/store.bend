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
    case St.Store{n, rs, m, gs}:
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

# Handlers
# --------

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
