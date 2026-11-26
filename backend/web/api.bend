import Base

import ../core/types.bend as T
import ../core/lifecycle.bend as Life
import ./json.bend as J
import ./schema.bend as S
import ./store.bend as St
import ./utf8.bend as U

# The route table and the HTTP layer around it. Every route is a value here,
# holding its method, path, operation id, request body and the answers it can
# give. A handler's result type, the codecs and the OpenAPI spec all come from
# that value, so they can't drift apart. A path segment written {name} is a
# path parameter, and matches any segment that isn't empty.
#
# Still to come: query parameters and auth rules.

type Method is Data:
  Get{}
  Head{}
  Post{}
  Put{}
  Patch{}
  Delete{}
  Other{}

def Method.name(m: Method) -> String:
  match m:
    case Get{}:
      "GET"
    case Head{}:
      "HEAD"
    case Post{}:
      "POST"
    case Put{}:
      "PUT"
    case Patch{}:
      "PATCH"
    case Delete{}:
      "DELETE"
    case Other{}:
      "OTHER"

# The key OpenAPI uses for the method.
def Method.key(m: Method) -> String:
  match m:
    case Get{}:
      "get"
    case Head{}:
      "head"
    case Post{}:
      "post"
    case Put{}:
      "put"
    case Patch{}:
      "patch"
    case Delete{}:
      "delete"
    case Other{}:
      "other"

# Other never matches, so an unknown method gets a 405 or a 404 from the path.
def Method.same(a: Method, b: Method) -> Bool:
  match a b:
    case Get{} Get{}:
      True{}
    case Head{} Head{}:
      True{}
    case Post{} Post{}:
      True{}
    case Put{} Put{}:
      True{}
    case Patch{} Patch{}:
      True{}
    case Delete{} Delete{}:
      True{}
    case _ _:
      False{}

# Whether a request with method asked can use a route with method m. HEAD can
# use any GET route, as RFC 9110 asks, so the route table never lists HEAD.
def Method.serves(asked: Method, m: Method) -> Bool:
  match asked m:
    case Head{} Get{}:
      True{}
    case a b:
      Method.same(a, b)

def Method.is_head(m: Method) -> Bool:
  match m:
    case Head{}:
      True{}
    case other:
      False{}

# A method as a 405's Allow header lists it, with HEAD wherever GET is.
def Method.allows(m: Method) -> String:
  match m:
    case Get{}:
      "GET, HEAD"
    case other:
      Method.name(other)

def Method.pick(same: Bool, m: Method, rest: Method) -> Method:
  match same:
    case True{}:
      m
    case False{}:
      rest

def Method.parse(+s: String) -> Method:
  Method.pick(J.Text.same(s, "GET"), Get{},
    Method.pick(J.Text.same(s, "POST"), Post{},
      Method.pick(J.Text.same(s, "HEAD"), Head{},
      Method.pick(J.Text.same(s, "PUT"), Put{},
        Method.pick(J.Text.same(s, "PATCH"), Patch{},
          Method.pick(J.Text.same(s, "DELETE"), Delete{}, Other{}))))))

# The statuses the API answers with. A status is a value with its own reason
# phrase, so a response can't go out with a code the reason table doesn't know.
# There's no 204, because every answer has a JSON body.
type Status is Data:
  OK{}
  Created{}
  BadRequest{}
  Unauthorized{}
  Forbidden{}
  NotFound{}
  MethodNotAllowed{}
  Conflict{}
  Unprocessable{}
  ServerError{}

def Status.code(s: Status) -> Nat:
  match s:
    case OK{}:
      200n
    case Created{}:
      201n
    case BadRequest{}:
      400n
    case Unauthorized{}:
      401n
    case Forbidden{}:
      403n
    case NotFound{}:
      404n
    case MethodNotAllowed{}:
      405n
    case Conflict{}:
      409n
    case Unprocessable{}:
      422n
    case ServerError{}:
      500n

def Status.reason(s: Status) -> String:
  match s:
    case OK{}:
      "OK"
    case Created{}:
      "Created"
    case BadRequest{}:
      "Bad Request"
    case Unauthorized{}:
      "Unauthorized"
    case Forbidden{}:
      "Forbidden"
    case NotFound{}:
      "Not Found"
    case MethodNotAllowed{}:
      "Method Not Allowed"
    case Conflict{}:
      "Conflict"
    case Unprocessable{}:
      "Unprocessable Content"
    case ServerError{}:
      "Internal Server Error"

# A status a route can answer with, and the schema of its body.
type Answer is Data:
  Answer{status: Status, description: String, schema: S.Schema}

# writes says whether the route's handler can change the store, so the shell
# can answer it with a 500 when the log can't be written.
type Route is Data:
  Route{method: Method, path: String, id: String, summary: String, body: Maybe<&2, S.Schema>, writes: Bool, answers: List<&2, Answer>}

def Route.method(r: Route) -> Method:
  match r:
    case Route{m, p, i, s, b, w, a}:
      m

def Route.path(r: Route) -> String:
  match r:
    case Route{m, p, i, s, b, w, a}:
      p

def Route.body(r: Route) -> Maybe<&2, S.Schema>:
  match r:
    case Route{m, p, i, s, b, w, a}:
      b

def Route.writes(r: Route) -> Bool:
  match r:
    case Route{m, p, i, s, b, w, a}:
      w

def Route.answers(r: Route) -> List<&2, Answer>:
  match r:
    case Route{m, p, i, s, b, w, a}:
      a

# Replies
# -------

# What a handler hands back: one of the route's answers, with a value of that
# answer's schema. Done picks the first answer and Fail moves on to the rest,
# so a reply can only be something the route declares.
def Reply(as: List<&2, Answer>) -> Data:
  match as:
    case Nil{}:
      Empty
    case Con{Answer{st, d, s}, rest}:
      Result<&2, &2, Reply(rest), S.Value(s)>

def Reply.status(as: List<&2, Answer>, r: Reply(as)) -> Nat:
  match as:
    case Nil{}:
      Empty.absurd(Nat, r)
    case Con{Answer{st, d, s}, rest}:
      match r:
        case Done{v}:
          Status.code(st)
        case Fail{x}:
          Reply.status(rest, x)

# The reply's status as a value, for its reason phrase.
def Reply.state(as: List<&2, Answer>, r: Reply(as)) -> Status:
  match as:
    case Nil{}:
      Empty.absurd(Status, r)
    case Con{Answer{st, d, s}, rest}:
      match r:
        case Done{v}:
          st
        case Fail{x}:
          Reply.state(rest, x)

def Reply.body(as: List<&2, Answer>, r: Reply(as)) -> J.Json:
  match as:
    case Nil{}:
      Empty.absurd(J.Json, r)
    case Con{Answer{st, d, s}, rest}:
      match r:
        case Done{v}:
          S.encode(s, v)
        case Fail{x}:
          Reply.body(rest, x)

# Every number in the reply's value is in range, as S.Schema.within says.
def Reply.within(as: List<&2, Answer>, r: Reply(as)) -> Bool:
  match as:
    case Nil{}:
      Empty.absurd(Bool, r)
    case Con{Answer{st, d, s}, rest}:
      match r:
        case Done{v}:
          S.Schema.within(s, v)
        case Fail{x}:
          Reply.within(rest, x)

# Whether a status and body fit one of the answers: the status matches and the
# body decodes under that answer's schema. Contract tests ask the same question
# of real responses.
def Answers.accepts(as: List<&2, Answer>, +status: Nat, +j: J.Json) -> Bool:
  match as:
    case Nil{}:
      False{}
    case Con{Answer{st, d, s}, rest}:
      Bool.and(Nat.is_eq(Status.code(st), status), Maybe.is_some(&2, S.Value(s), S.decode(s, j))) || Answers.accepts(rest, status, j)

def Answers.distinct(as: List<&2, Answer>) -> Bool:
  match as:
    case Nil{}:
      True{}
    case Con{Answer{st, d, s}, rest}:
      S.Schema.distinct(s) && Answers.distinct(rest)

# No answer's schema holds a number, so every reply is in range whatever its
# values are.
def Answers.free(as: List<&2, Answer>) -> Bool:
  match as:
    case Nil{}:
      True{}
    case Con{Answer{st, d, s}, rest}:
      S.Schema.free(s) && Answers.free(rest)

def Answers.wellformed(as: List<&2, Answer>) -> Bool:
  match as:
    case Nil{}:
      True{}
    case Con{Answer{st, d, s}, rest}:
      S.Schema.wellformed(s) && Answers.wellformed(rest)

# Schemas
# -------

def Schemas.health() -> S.Schema:
  S.Schema.obj("Health", S.SField{"status", S.SStr{}, S.SEnd{}})

# Every error body. error is a stable code for programs, detail is for people.
def Schemas.error() -> S.Schema:
  S.Schema.obj("Error", S.SField{"error", S.SStr{}, S.SOpt{"detail", S.SStr{}, S.SEnd{}}})

# The route table
# ---------------

# The routes, without the data a request brings. Api.ops lists them, and the
# spec and the dispatcher walk that list.
type Endpoint is Data:
  EHealth{}
  ECreate{}
  EFetch{}
  ECancel{}

def Endpoint.route(e: Endpoint) -> Route:
  match e:
    case EHealth{}:
      Route{Get{}, "/api/health", "getHealth", "Whether the web process is up", None{}, False{},
        [Answer{OK{}, "The web process is up", Schemas.health()}]}
    case ECreate{}:
      Route{Post{}, "/api/v1/appraisals", "createAppraisal", "Request an appraisal. Sending the same key again is safe", Some{St.Schemas.draft()}, True{},
        [Answer{Created{}, "The appraisal was requested", St.Schemas.appraisal()},
         Answer{OK{}, "An appraisal with this key was already requested, so nothing changed", St.Schemas.appraisal()},
         Answer{Unprocessable{}, "The request breaks a rule, which error names", Schemas.error()}]}
    case EFetch{}:
      Route{Get{}, "/api/v1/appraisals/{id}", "getAppraisal", "Read an appraisal", None{}, False{},
        [Answer{OK{}, "The appraisal", St.Schemas.appraisal()},
         Answer{NotFound{}, "No appraisal has this id", Schemas.error()}]}
    case ECancel{}:
      Route{Post{}, "/api/v1/appraisals/{id}/cancel", "cancelAppraisal", "Cancel an appraisal. Cancelling one that's already cancelled changes nothing", None{}, True{},
        [Answer{OK{}, "The appraisal, now cancelled", St.Schemas.appraisal()},
         Answer{NotFound{}, "No appraisal has this id", Schemas.error()},
         Answer{Conflict{}, "The appraisal is underway or completed, so it can't be cancelled", Schemas.error()}]}

# A request with what the handler needs from the store already looked up, so
# the handlers stay pure and the laws cover every store they could meet.
# Create carries the draft, the record already stored under its key if any,
# and the id a new record would get.
type Op is Data:
  Health{}
  Create{draft: St.Draft, known: Maybe<&2, St.Rec>, id: String}
  Fetch{found: Maybe<&2, St.Rec>}
  Cancel{found: Maybe<&2, St.Rec>}

def Op.endpoint(op: Op) -> Endpoint:
  match op:
    case Health{}:
      EHealth{}
    case Create{d, k, i}:
      ECreate{}
    case Fetch{f}:
      EFetch{}
    case Cancel{f}:
      ECancel{}

def Op.route(op: Op) -> Route:
  Endpoint.route(Op.endpoint(op))

def Api.ops() -> List<&2, Endpoint>:
  [EHealth{}, ECreate{}, EFetch{}, ECancel{}]

def Api.routes(ops: List<&2, Endpoint>) -> List<&2, Route>:
  match ops:
    case Nil{}:
      []
    case Con{op, rest}:
      Endpoint.route(op) <> Api.routes(rest)

# Handlers
# --------

def Api.fail(code: String, detail: String) -> S.Value(Schemas.error()):
  (code, (Some{detail}, Unit{}))

def CreateReply() -> Data:
  Reply(Route.answers(Endpoint.route(ECreate{})))

def FetchReply() -> Data:
  Reply(Route.answers(Endpoint.route(EFetch{})))

def CancelReply() -> Data:
  Reply(Route.answers(Endpoint.route(ECancel{})))

def Create.fresh(p: Maybe<&2, St.Problem>, d: St.Draft, id: String) -> CreateReply():
  match p:
    case None{}:
      Done{St.Rec.value(St.Rec.new(id, d))}
    case Some{St.Problem{code, detail}}:
      Fail{Fail{Done{Api.fail(code, detail)}}}

def Create.reply(known: Maybe<&2, St.Rec>, +d: St.Draft, id: String) -> CreateReply():
  match known:
    case Some{r}:
      Fail{Done{St.Rec.value(r)}}
    case None{}:
      Create.fresh(St.Draft.problem(d), d, id)

def Fetch.reply(found: Maybe<&2, St.Rec>) -> FetchReply():
  match found:
    case Some{r}:
      Done{St.Rec.value(r)}
    case None{}:
      Fail{Done{Api.fail("not_found", "No appraisal has this id")}}

def Cancel.next(m: Maybe<&2, T.Status>, r: St.Rec) -> CancelReply():
  match m:
    case Some{s}:
      Done{St.Rec.value(St.Rec.with(r, s))}
    case None{}:
      Fail{Fail{Done{Api.fail("locked", "The appraisal is underway or completed, so it can't be cancelled")}}}

def Cancel.pick(done: Bool, +r: St.Rec) -> CancelReply():
  match done:
    case True{}:
      Done{St.Rec.value(r)}
    case False{}:
      Cancel.next(Life.step(St.Rec.status(r), Life.Cancel{}), r)

def Cancel.reply(found: Maybe<&2, St.Rec>) -> CancelReply():
  match found:
    case Some{+r}:
      Cancel.pick(St.Status.is_cancelled(St.Rec.status(r)), r)
    case None{}:
      Fail{Done{Api.fail("not_found", "No appraisal has this id")}}

# The handlers. Each one's type comes from its route, so a reply the route
# doesn't declare is a type error.
def Api.run(op: Op) -> Reply(Route.answers(Op.route(op))):
  match op:
    case Health{}:
      Done{("ok", Unit{})}
    case Create{d, known, id}:
      Create.reply(known, d, id)
    case Fetch{found}:
      Fetch.reply(found)
    case Cancel{found}:
      Cancel.reply(found)

# The status code a handler answers with.
def Op.status(+op: Op) -> Nat:
  Reply.status(Route.answers(Op.route(op)), Api.run(op))

# What the log records for a request, if anything. The shell writes it before
# it sends the reply, so a reply the client saw is never lost to a crash.
def Create.made(p: Maybe<&2, St.Problem>, d: St.Draft, id: String) -> Maybe<&2, St.Change>:
  match p:
    case None{}:
      Some{St.Requested{St.Rec.new(id, d)}}
    case Some{x}:
      None{}

def Create.change(known: Maybe<&2, St.Rec>, +d: St.Draft, id: String) -> Maybe<&2, St.Change>:
  match known:
    case Some{r}:
      None{}
    case None{}:
      Create.made(St.Draft.problem(d), d, id)

def Cancel.made(m: Maybe<&2, T.Status>, id: String) -> Maybe<&2, St.Change>:
  match m:
    case Some{s}:
      Some{St.Cancelled{id}}
    case None{}:
      None{}

def Cancel.change(found: Maybe<&2, St.Rec>) -> Maybe<&2, St.Change>:
  match found:
    case Some{+r}:
      Cancel.made(Life.step(St.Rec.status(r), Life.Cancel{}), St.Rec.id(r))
    case None{}:
      None{}

def Api.change(op: Op) -> Maybe<&2, St.Change>:
  match op:
    case Create{d, known, id}:
      Create.change(known, d, id)
    case Cancel{found}:
      Cancel.change(found)
    case other:
      None{}

# HTTP
# ----

type Cut is Data:
  Cut{head: String, tail: String}

# c onto acc, unless it's the stop character, which is dropped.
def Text.keep(hit: Bool, c: Char, acc: String) -> String:
  match hit:
    case True{}:
      acc
    case False{}:
      SCon{c, acc}

# Scans s for the stop character, with the text before it reversed in acc. hit
# says the character just read was the stop, so the scan ends there and reads
# no further. Tail recursive, so a long request costs no stack.
def Text.cut.go(+stop: Nat, s: String, hit: Bool, acc: String) -> Maybe<&2, Cut>:
  match s hit:
    case rest True{}:
      Some{Cut{String.reverse(acc), rest}}
    case SNil{} False{}:
      None{}
    case SCon{+c, t} False{}:
      Text.cut.go(stop, t, Nat.is_eq(J.Text.code(c), stop), Text.keep(Nat.is_eq(J.Text.code(c), stop), c, acc))

# Splits s at the first character with code stop, which is dropped. None if s
# has no such character.
def Text.cut(+stop: Nat, s: String) -> Maybe<&2, Cut>:
  Text.cut.go(stop, s, False{}, "")

def Text.before.go(+stop: Nat, s: String, hit: Bool, acc: String) -> String:
  match s hit:
    case rest True{}:
      String.reverse(acc)
    case SNil{} False{}:
      String.reverse(acc)
    case SCon{+c, t} False{}:
      Text.before.go(stop, t, Nat.is_eq(J.Text.code(c), stop), Text.keep(Nat.is_eq(J.Text.code(c), stop), c, acc))

# s up to the first character with code stop, or all of s.
def Text.before(+stop: Nat, s: String) -> String:
  Text.before.go(stop, s, False{}, "")

# A request line: the method and the path, with any query string dropped.
type Line is Data:
  Line{method: Method, path: String}

def Http.version.pick(ok: Bool, m: String, target: String) -> Maybe<&2, Line>:
  match ok:
    case True{}:
      Some{Line{Method.parse(m), Text.before(63n, target)}}
    case False{}:
      None{}

def Http.version(m: String, target: String, rest: String) -> Maybe<&2, Line>:
  Http.version.pick(String.starts_with(rest, "HTTP/1."), m, target)

def Http.target(m: String, cut: Maybe<&2, Cut>) -> Maybe<&2, Line>:
  match cut:
    case Some{Cut{target, rest}}:
      Http.version(m, target, rest)
    case None{}:
      None{}

def Http.method(cut: Maybe<&2, Cut>) -> Maybe<&2, Line>:
  match cut:
    case Some{Cut{m, rest}}:
      Http.target(m, Text.cut(32n, rest))
    case None{}:
      None{}

# Whether s starts with a CR or an LF.
def Text.blank(s: String) -> Bool:
  match s:
    case SCon{+c, t}:
      Nat.is_eq(J.Text.code(c), 13n) || Nat.is_eq(J.Text.code(c), 10n)
    case SNil{}:
      False{}

# s without its leading CRs and LFs. hit says s starts with one.
def Text.skip.go(s: String, hit: Bool) -> String:
  match s hit:
    case SCon{c, +t} True{}:
      Text.skip.go(t, Text.blank(t))
    case rest other:
      rest

def Text.skip(+s: String) -> String:
  Text.skip.go(s, Text.blank(s))

def Http.line(text: String) -> Maybe<&2, Line>:
  Http.method(Text.cut(32n, text))

def Http.body(send: Bool, body: String) -> String:
  match send:
    case True{}:
      body
    case False{}:
      ""

# One response. The web process closes each connection after it answers. A
# HEAD request gets the same headers with no body, so send is False for it.
def Http.response(+status: Status, headers: String, +body: String, send: Bool) -> String:
  "HTTP/1.1 " ++ Nat.show(Status.code(status)) ++ " " ++ Status.reason(status)
    ++ "\r\nConnection: close\r\nContent-Type: application/json\r\nContent-Length: "
    ++ Nat.show(J.Text.bytes(body, 0n)) ++ "\r\n" ++ headers ++ "\r\n" ++ Http.body(send, body)

# Errors from the dispatcher use the Error schema, so they're typed like any
# other answer.
def Api.error.body(code: String) -> J.Json:
  S.encode(Schemas.error(), (code, (None{}, Unit{})))

def Api.error(status: Status, headers: String, code: String, send: Bool) -> String:
  Http.response(status, headers, J.Json.print(Api.error.body(code)), send)

def Api.reply(+op: Op, send: Bool) -> String:
  Http.response(Reply.state(Route.answers(Op.route(op)), Api.run(op)), "",
    J.Json.print(Reply.body(Route.answers(Op.route(op)), Api.run(op))), send)

# Request bodies
# --------------

# s after the first blank line, the end of the headers, or "" if there's none.
# hit says s starts with the blank line. Tail recursive, like Text.cut.
def Http.payload.go(s: String, hit: Bool) -> String:
  match s hit:
    case rest True{}:
      String.drop(rest, 4n)
    case SNil{} False{}:
      ""
    case SCon{c, +t} False{}:
      Http.payload.go(t, String.starts_with(t, "\r\n\r\n"))

def Http.payload(+text: String) -> String:
  Http.payload.go(text, String.starts_with(text, "\r\n\r\n"))

def Http.head.go(s: String, hit: Bool, acc: String) -> String:
  match s hit:
    case rest True{}:
      String.reverse(acc)
    case SNil{} False{}:
      String.reverse(acc)
    case SCon{+c, +t} False{}:
      Http.head.go(t, String.starts_with(t, "\r\n\r\n"), SCon{c, acc})

# The request line and headers, without the blank line after them.
def Http.head(+text: String) -> String:
  Http.head.go(text, String.starts_with(text, "\r\n\r\n"), "")

def Http.length.pick(hit: Bool, line: String, rest: Nat) -> Nat:
  match hit:
    case True{}:
      Maybe.default(&2, Nat, Nat.read(String.trim(String.drop(line, 15n))), 0n)
    case False{}:
      rest

# The Content-Length header's value, or 0. Header names ignore case.
def Http.length(lines: List<&2, String>) -> Nat:
  match lines:
    case Nil{}:
      0n
    case Con{+line, rest}:
      Http.length.pick(String.starts_with(String.to_lower(line), "content-length:"), line, Http.length(rest))

# Whether the bytes read so far hold the whole request. The shell holds bytes,
# because a String can't count a character cut in two at the end of a read.

# The byte that would carry a run of CR LF CR LF on: CR after none or two,
# LF after one or three.
def Http.expect(run: Nat) -> Nat:
  match run:
    case 0n:
      13n
    case 1n:
      10n
    case 2n:
      13n
    case _:
      10n

def Http.run.pick(same: Bool, run: Nat, cr: Bool) -> Nat:
  match same cr:
    case True{} _:
      Nat.add(run, 1n)
    case False{} True{}:
      1n
    case False{} False{}:
      0n

# How much of CR LF CR LF ends at byte b, given how much ended just before it.
def Http.run(+run: Nat, +b: Nat) -> Nat:
  Http.run.pick(Nat.is_eq(b, Http.expect(run)), run, Nat.is_eq(b, 13n))

# The number of bytes up to and including the blank line after the headers.
def Http.mark(fuel: Nat, bs: List<&2, U32>, pos: Nat, run: Nat, hit: Bool) -> Maybe<&2, Nat>:
  match fuel bs hit:
    case _ _ True{}:
      Some{pos}
    case 0n _ False{}:
      None{}
    case 1n+f Nil{} False{}:
      None{}
    case 1n+f Con{b, rest} False{}:
      +r = Http.run(run, U32.to_nat(b))
      Http.mark(f, rest, Nat.add(pos, 1n), r, Nat.is_eq(r, 4n))

def Http.ready.at(m: Maybe<&2, Nat>, +bs: List<&2, U32>, +total: Nat) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{+p}:
      Nat.is_le(Nat.add(p, Http.length(String.lines(U.Utf8.decode(List.take(&2, U32, bs, p))))), total)

def Http.ready.go(+bs: List<&2, U32>, +total: Nat) -> Bool:
  Http.ready.at(Http.mark(total, bs, 0n, 0n, False{}), bs, total)

# Whether bs starts with a CR or an LF byte.
def Http.lead.blank(bs: List<&2, U32>) -> Bool:
  match bs:
    case Con{+b, t}:
      Nat.is_eq(U32.to_nat(b), 13n) || Nat.is_eq(U32.to_nat(b), 10n)
    case Nil{}:
      False{}

# bs without its leading CR and LF bytes. hit says bs starts with one.
def Http.lead.go(bs: List<&2, U32>, hit: Bool) -> List<&2, U32>:
  match bs hit:
    case Con{b, +t} True{}:
      Http.lead.go(t, Http.lead.blank(t))
    case rest other:
      rest

def Http.lead(+bs: List<&2, U32>) -> List<&2, U32>:
  Http.lead.go(bs, Http.lead.blank(bs))

def Http.ready.from(+bs: List<&2, U32>) -> Bool:
  Http.ready.go(bs, List.length(&2, U32, bs))

# Whether bs holds a whole request: its headers have ended, after any empty
# lines before the request line, and the body has Content-Length bytes.
def Http.ready(+bs: List<&2, U32>) -> Bool:
  Http.ready.from(Http.lead(bs))

# Paths
# -----

def Path.is_param(s: String) -> Bool:
  String.starts_with(s, "{")

def Path.keep(empty: Bool, seg: String, ps: List<&2, String>) -> Maybe<&2, List<&2, String>>:
  match empty:
    case True{}:
      None{}
    case False{}:
      Some{seg <> ps}

def Path.take(param: Bool, +seg: String, ok: Bool, ps: List<&2, String>) -> Maybe<&2, List<&2, String>>:
  match param ok:
    case True{} _:
      Path.keep(String.is_empty(seg), seg, ps)
    case False{} True{}:
      Some{ps}
    case False{} False{}:
      None{}

# One template segment against one path segment, with the parameters so far
# in reverse.
def Path.step(+t: String, +seg: String, acc: Maybe<&2, List<&2, String>>) -> Maybe<&2, List<&2, String>>:
  match acc:
    case None{}:
      None{}
    case Some{ps}:
      Path.take(Path.is_param(t), seg, J.Text.same(t, seg), ps)

def Path.segs(ts: List<&2, String>, ss: List<&2, String>, acc: Maybe<&2, List<&2, String>>) -> Maybe<&2, List<&2, String>>:
  match ts ss:
    case Nil{} Nil{}:
      acc
    case Con{t, tr} Con{s, sr}:
      Path.segs(tr, sr, Path.step(t, s, acc))
    case _ _:
      None{}

def Path.order(m: Maybe<&2, List<&2, String>>) -> Maybe<&2, List<&2, String>>:
  match m:
    case None{}:
      None{}
    case Some{ps}:
      Some{List.reverse(&2, String, ps)}

# The path's parameters, in order, if it fits the route's template.
def Path.match(template: String, path: String) -> Maybe<&2, List<&2, String>>:
  Path.order(Path.segs(String.split(template, J.Text.char(47n)), String.split(path, J.Text.char(47n)), Some{[]}))

def Path.fits(template: String, path: String) -> Bool:
  Maybe.is_some(&2, List<&2, String>, Path.match(template, path))

def Path.first(ps: List<&2, String>) -> String:
  match ps:
    case Nil{}:
      ""
    case Con{p, rest}:
      p

# Dispatch
# --------

# A matched route and its path parameters.
type Hit is Data:
  Hit{endpoint: Endpoint, params: List<&2, String>}

def Api.hit.pick(serves: Bool, ep: Endpoint, params: Maybe<&2, List<&2, String>>, rest: Maybe<&2, Hit>) -> Maybe<&2, Hit>:
  match serves params:
    case True{} Some{ps}:
      Some{Hit{ep, ps}}
    case _ _:
      rest

# The first route with this method and a template the path fits.
def Api.hit(+m: Method, +path: String, ops: List<&2, Endpoint>) -> Maybe<&2, Hit>:
  match ops:
    case Nil{}:
      None{}
    case Con{+op, rest}:
      Api.hit.pick(Method.serves(m, Route.method(Endpoint.route(op))), op, Path.match(Route.path(Endpoint.route(op)), path), Api.hit(m, path, rest))

def Api.allow.pick(same: Bool, m: Method, more: Bool, rest: String) -> String:
  match same more:
    case True{} True{}:
      Method.allows(m) ++ ", " ++ rest
    case True{} False{}:
      Method.allows(m) ++ rest
    case False{} _:
      rest

def Api.allow.more(+path: String, ops: List<&2, Endpoint>) -> Bool:
  match ops:
    case Nil{}:
      False{}
    case Con{op, rest}:
      Path.fits(Route.path(Endpoint.route(op)), path) || Api.allow.more(path, rest)

# The methods the table has for path, for a 405's Allow header. Empty if no
# route's template fits the path.
def Api.allow(+path: String, ops: List<&2, Endpoint>) -> String:
  match ops:
    case Nil{}:
      ""
    case Con{+op, +rest}:
      Api.allow.pick(Path.fits(Route.path(Endpoint.route(op)), path), Route.method(Endpoint.route(op)),
        Api.allow.more(path, rest), Api.allow(path, rest))

def Api.missing(allow: String, send: Bool) -> String:
  match allow:
    case SNil{}:
      Api.error(NotFound{}, "", "not_found", send)
    case SCon{c, t}:
      Api.error(MethodNotAllowed{}, "Allow: " ++ SCon{c, t} ++ "\r\n", "method_not_allowed", send)

def Api.json(s: String) -> Maybe<&2, J.Json>:
  J.Json.parse(s)

def Api.draft.of(m: Maybe<&2, S.Value(St.Schemas.draft())>) -> Maybe<&2, St.Draft>:
  match m:
    case None{}:
      None{}
    case Some{v}:
      Some{St.Draft.of(v)}

def Api.draft.json(m: Maybe<&2, J.Json>) -> Maybe<&2, St.Draft>:
  match m:
    case None{}:
      None{}
    case Some{+j}:
      Api.draft.of(S.decode(St.Schemas.draft(), j))

# A body that isn't a NewAppraisal is refused before any handler sees it.
def Api.draft(body: String) -> Maybe<&2, St.Draft>:
  Api.draft.json(Api.json(body))

def Api.create(m: Maybe<&2, St.Draft>, +store: St.Store) -> Maybe<&2, Op>:
  match m:
    case None{}:
      None{}
    case Some{+d}:
      Some{Create{d, St.Store.by_key(St.Draft.key(d), St.Store.recs(store)), St.Store.next(store)}}

# Looks up what the handler needs from the store. None if the body is wrong.
def Api.resolve(ep: Endpoint, params: List<&2, String>, body: String, +store: St.Store) -> Maybe<&2, Op>:
  match ep:
    case EHealth{}:
      Some{Health{}}
    case ECreate{}:
      Api.create(Api.draft(body), store)
    case EFetch{}:
      Some{Fetch{St.Store.find(Path.first(params), St.Store.recs(store))}}
    case ECancel{}:
      Some{Cancel{St.Store.find(Path.first(params), St.Store.recs(store))}}

# The response, and the change the log has to record before it's sent.
type Handled is Data:
  Handled{response: String, change: Maybe<&2, St.Change>}

def Api.resolved(m: Maybe<&2, Op>, send: Bool) -> Handled:
  match m:
    case Some{+op}:
      Handled{Api.reply(op, send), Api.change(op)}
    case None{}:
      Handled{Api.error(BadRequest{}, "", "invalid_body", send), None{}}

def Api.found(hit: Maybe<&2, Hit>, allow: String, send: Bool, body: String, +store: St.Store) -> Handled:
  match hit:
    case Some{Hit{ep, ps}}:
      Api.resolved(Api.resolve(ep, ps, body, store), send)
    case None{}:
      Handled{Api.missing(allow, send), None{}}

def Api.dispatch(line: Maybe<&2, Line>, body: String, +store: St.Store) -> Handled:
  match line:
    case Some{Line{+m, +path}}:
      Api.found(Api.hit(m, path, Api.ops()), Api.allow(path, Api.ops()), Bool.not(Method.is_head(m)), body, store)
    case None{}:
      Handled{Api.error(BadRequest{}, "", "bad_request", True{}), None{}}

def Api.handled(+text: String, +store: St.Store) -> Handled:
  Api.dispatch(Http.line(text), Http.payload(text), store)

# The whole web handler: request text and the store in, the response and the
# change to log out. Empty lines before the request line are ignored, as RFC
# 9112 asks, so they can't be taken for the end of the headers either.
def Api.handle(+text: String, +store: St.Store) -> Handled:
  Api.handled(Text.skip(text), store)

def Handled.response(h: Handled) -> String:
  match h:
    case Handled{r, c}:
      r

def Handled.change(h: Handled) -> Maybe<&2, St.Change>:
  match h:
    case Handled{r, c}:
      c

# A 500 for when the log can't be written. Nothing was stored, so the client
# can send the request again.
def Api.unsaved() -> String:
  Api.error(ServerError{}, "", "not_saved", True{})
