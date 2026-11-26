import Base

import ./json.bend as J
import ./schema.bend as S

# The route table and the HTTP layer around it. Every route is a value here,
# holding its method, path, operation id and the answers it can give. A
# handler's result type, the codecs and the OpenAPI spec all come from that
# value, so they can't drift apart.
#
# Still to come: request bodies, path and query parameters, and auth rules.

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

type Route is Data:
  Route{method: Method, path: String, id: String, summary: String, answers: List<&2, Answer>}

def Route.method(r: Route) -> Method:
  match r:
    case Route{m, p, i, s, a}:
      m

def Route.path(r: Route) -> String:
  match r:
    case Route{m, p, i, s, a}:
      p

def Route.answers(r: Route) -> List<&2, Answer>:
  match r:
    case Route{m, p, i, s, a}:
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

type Op is Data:
  Health{}

def Op.route(op: Op) -> Route:
  match op:
    case Health{}:
      Route{Get{}, "/api/health", "getHealth", "Whether the web process is up",
        [Answer{OK{}, "The web process is up", Schemas.health()}]}

def Api.ops() -> List<&2, Op>:
  [Health{}]

def Api.routes(ops: List<&2, Op>) -> List<&2, Route>:
  match ops:
    case Nil{}:
      []
    case Con{op, rest}:
      Op.route(op) <> Api.routes(rest)

# The handlers. Each one's type comes from its route, so a reply the route
# doesn't declare is a type error.
def Api.run(op: Op) -> Reply(Route.answers(Op.route(op))):
  match op:
    case Health{}:
      Done{("ok", Unit{})}

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

# Empty lines before the request line are ignored, as RFC 9112 asks.
def Http.line(text: String) -> Maybe<&2, Line>:
  Http.method(Text.cut(32n, Text.skip(text)))

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

# Dispatch
# --------

def Api.hit.pick(hit: Bool, op: Op, rest: Maybe<&2, Op>) -> Maybe<&2, Op>:
  match hit:
    case True{}:
      Some{op}
    case False{}:
      rest

# The first operation with this method and path.
def Api.hit(+m: Method, +path: String, ops: List<&2, Op>) -> Maybe<&2, Op>:
  match ops:
    case Nil{}:
      None{}
    case Con{+op, rest}:
      Api.hit.pick(Method.serves(m, Route.method(Op.route(op))) && J.Text.same(path, Route.path(Op.route(op))), op, Api.hit(m, path, rest))

def Api.allow.pick(same: Bool, m: Method, more: Bool, rest: String) -> String:
  match same more:
    case True{} True{}:
      Method.allows(m) ++ ", " ++ rest
    case True{} False{}:
      Method.allows(m) ++ rest
    case False{} _:
      rest

def Api.allow.more(+path: String, ops: List<&2, Op>) -> Bool:
  match ops:
    case Nil{}:
      False{}
    case Con{op, rest}:
      J.Text.same(path, Route.path(Op.route(op))) || Api.allow.more(path, rest)

# The methods the table has for path, for a 405's Allow header. Empty if the
# path isn't in the table.
def Api.allow(+path: String, ops: List<&2, Op>) -> String:
  match ops:
    case Nil{}:
      ""
    case Con{+op, +rest}:
      Api.allow.pick(J.Text.same(path, Route.path(Op.route(op))), Route.method(Op.route(op)),
        Api.allow.more(path, rest), Api.allow(path, rest))

def Api.missing(allow: String, send: Bool) -> String:
  match allow:
    case SNil{}:
      Api.error(NotFound{}, "", "not_found", send)
    case SCon{c, t}:
      Api.error(MethodNotAllowed{}, "Allow: " ++ SCon{c, t} ++ "\r\n", "method_not_allowed", send)

def Api.found(hit: Maybe<&2, Op>, allow: String, send: Bool) -> String:
  match hit:
    case Some{op}:
      Api.reply(op, send)
    case None{}:
      Api.missing(allow, send)

def Api.dispatch(line: Maybe<&2, Line>) -> String:
  match line:
    case Some{Line{+m, +path}}:
      Api.found(Api.hit(m, path, Api.ops()), Api.allow(path, Api.ops()), Bool.not(Method.is_head(m)))
    case None{}:
      Api.error(BadRequest{}, "", "bad_request", True{})

# The whole web handler: request text in, response text out.
def Api.handle(text: String) -> String:
  Api.dispatch(Http.line(text))
