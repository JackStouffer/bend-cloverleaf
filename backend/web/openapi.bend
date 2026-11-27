import Base

import ./json.bend as J
import ./schema.bend as S
import ./api.bend as A

# Builds the OpenAPI 3.1 document from the route table. Pure, so web/spec.bend
# only prints it, and the laws can check it.
#
# Every object and enum schema becomes a named component and is referred to by
# $ref, so the generated TypeScript gets readable type names. Objects are closed with
# additionalProperties false, because the decoder refuses unknown fields.

def Spec.obj1(k: String, v: J.Json) -> J.Json:
  J.JObj{J.JField{k, v, J.JNil{}}}

def Spec.type(name: String) -> J.Json:
  Spec.obj1("type", J.JStr{name})

# A schema where it's used. Objects are references to their component, and a
# row on its own is never used.
def Spec.ref(s: S.Schema) -> J.Json:
  match s:
    case S.SStr{}:
      Spec.type("string")
    case S.SNat{}:
      J.JObj{J.JField{"type", J.JStr{"integer"}, J.JField{"minimum", J.JNum{0n}, J.JField{"maximum", J.JNum{J.Json.Max()}, J.JNil{}}}}}
    case S.SBool{}:
      Spec.type("boolean")
    case S.SList{it}:
      J.JObj{J.JField{"type", J.JStr{"array"}, J.JField{"items", Spec.ref(it), J.JNil{}}}}
    case S.SItems{i}:
      Spec.ref(i)
    case S.SObj{n, r}:
      Spec.obj1("$ref", J.JStr{"#/components/schemas/" ++ n})
    case S.SEnum{n, vs}:
      Spec.obj1("$ref", J.JStr{"#/components/schemas/" ++ n})
    case other:
      J.JObj{J.JNil{}}

def Spec.props(row: S.Schema) -> J.Json:
  match row:
    case S.SField{k, f, r}:
      J.JField{k, Spec.ref(f), Spec.props(r)}
    case S.SOpt{k, f, r}:
      J.JField{k, Spec.ref(f), Spec.props(r)}
    case other:
      J.JNil{}

def Spec.required(row: S.Schema) -> J.Json:
  match row:
    case S.SField{k, f, r}:
      J.JCons{J.JStr{k}, Spec.required(r)}
    case S.SOpt{k, f, r}:
      Spec.required(r)
    case other:
      J.JNil{}

def Spec.object(+row: S.Schema) -> J.Json:
  J.JObj{J.JField{"type", J.JStr{"object"},
    J.JField{"properties", J.JObj{Spec.props(row)},
      J.JField{"required", J.JArr{Spec.required(row)},
        J.JField{"additionalProperties", J.JBool{False{}}, J.JNil{}}}}}}

def Spec.names(vs: List<&2, String>) -> J.Json:
  match vs:
    case Nil{}:
      J.JNil{}
    case Con{v, rest}:
      J.JCons{J.JStr{v}, Spec.names(rest)}

def Spec.enum(vs: List<&2, String>) -> J.Json:
  J.JObj{J.JField{"type", J.JStr{"string"}, J.JField{"enum", J.JArr{Spec.names(vs)}, J.JNil{}}}}

# Components
# ----------

# Every object in s, outer ones first, in reverse order onto acc.
def Spec.objs(s: S.Schema, acc: List<&2, S.Schema>) -> List<&2, S.Schema>:
  match s:
    case S.SList{it}:
      Spec.objs(it, acc)
    case S.SItems{i}:
      Spec.objs(i, acc)
    case S.SObj{+n, +r}:
      Spec.objs(r, S.SObj{n, r} <> acc)
    case S.SEnum{n, vs}:
      S.SEnum{n, vs} <> acc
    case S.SField{k, f, r}:
      Spec.objs(r, Spec.objs(f, acc))
    case S.SOpt{k, f, r}:
      Spec.objs(r, Spec.objs(f, acc))
    case other:
      acc

def Spec.answers(as: List<&2, A.Answer>, acc: List<&2, S.Schema>) -> List<&2, S.Schema>:
  match as:
    case Nil{}:
      acc
    case Con{A.Answer{st, d, s}, rest}:
      Spec.answers(rest, Spec.objs(s, acc))

def Spec.body(b: Maybe<&2, S.Schema>, acc: List<&2, S.Schema>) -> List<&2, S.Schema>:
  match b:
    case None{}:
      acc
    case Some{s}:
      Spec.objs(s, acc)

def Spec.walk(routes: List<&2, A.Route>, acc: List<&2, S.Schema>) -> List<&2, S.Schema>:
  match routes:
    case Nil{}:
      acc
    case Con{A.Route{m, p, i, sum, b, w, u, as}, rest}:
      Spec.walk(rest, Spec.answers(as, Spec.body(b, acc)))

# Every object the table uses, in order of first use, repeats included. The
# Error schema is always there, because the dispatcher can answer any request
# with it.
def Spec.all(routes: List<&2, A.Route>) -> List<&2, S.Schema>:
  List.reverse(&2, S.Schema, Spec.objs(A.Schemas.error(), Spec.walk(routes, [])))

def Spec.name(s: S.Schema) -> String:
  match s:
    case S.SObj{n, r}:
      n
    case S.SEnum{n, vs}:
      n
    case other:
      ""

def Spec.known(+s: S.Schema, xs: List<&2, S.Schema>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{x, rest}:
      J.Text.same(Spec.name(s), Spec.name(x)) || Spec.known(s, rest)

# Some other definition shares s's name.
def Spec.clash(+s: S.Schema, xs: List<&2, S.Schema>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{+x, rest}:
      Bool.and(J.Text.same(Spec.name(s), Spec.name(x)), Bool.not(S.Schema.same(s, x))) || Spec.clash(s, rest)

# Each name has one definition, so the components don't depend on which use
# came first.
def Spec.agree(xs: List<&2, S.Schema>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, +rest}:
      Bool.not(Spec.clash(x, rest)) && Spec.agree(rest)

def Spec.keep(known: Bool, x: S.Schema, seen: List<&2, S.Schema>) -> List<&2, S.Schema>:
  match known:
    case True{}:
      seen
    case False{}:
      List.append(&2, S.Schema, seen, [x])

def Spec.unique(xs: List<&2, S.Schema>, +seen: List<&2, S.Schema>) -> List<&2, S.Schema>:
  match xs:
    case Nil{}:
      seen
    case Con{+x, rest}:
      Spec.unique(rest, Spec.keep(Spec.known(x, seen), x, seen))

def Spec.components(xs: List<&2, S.Schema>) -> J.Json:
  match xs:
    case Nil{}:
      J.JNil{}
    case Con{S.SObj{n, r}, rest}:
      J.JField{n, Spec.object(r), Spec.components(rest)}
    case Con{S.SEnum{n, vs}, rest}:
      J.JField{n, Spec.enum(vs), Spec.components(rest)}
    case Con{other, rest}:
      Spec.components(rest)

# Paths
# -----

def Spec.content(s: S.Schema) -> J.Json:
  Spec.obj1("application/json", Spec.obj1("schema", Spec.ref(s)))

def Spec.response(d: String, s: S.Schema) -> J.Json:
  J.JObj{J.JField{"description", J.JStr{d}, J.JField{"content", Spec.content(s), J.JNil{}}}}

# The shell's 500, on a route that can write to the log.
def Spec.unsaved(writes: Bool) -> J.Json:
  match writes:
    case True{}:
      J.JField{"5XX", Spec.response("The change could not be saved, so nothing changed and the request can be sent again", A.Schemas.error()), J.JNil{}}
    case False{}:
      J.JNil{}

# A route that needs a key answers 401 without one and 403 with the other
# kind. The gate sends both before the route's own handler runs.
def Spec.denials(u: A.Auth, rest: J.Json) -> J.Json:
  match u:
    case A.Open{}:
      rest
    case other:
      J.JField{"401", Spec.response("No key, or a key nobody has", A.Schemas.error()),
        J.JField{"403", Spec.response("A key for the other kind of route", A.Schemas.error()), rest}}

# The route's own answers, then the gate's and the dispatcher's errors, then
# the shell's.
def Spec.responses(+writes: Bool, u: A.Auth, as: List<&2, A.Answer>) -> J.Json:
  match as:
    case Nil{}:
      Spec.denials(u, J.JField{"4XX", Spec.response("The request was refused", A.Schemas.error()), Spec.unsaved(writes)})
    case Con{A.Answer{st, d, s}, rest}:
      J.JField{Nat.show(A.Status.code(st)), Spec.response(d, s), Spec.responses(writes, u, rest)}

# A path segment {name} without its braces.
def Spec.param.name(+seg: String) -> String:
  String.take(String.drop(seg, 1n), Nat.sub(String.length(seg), 2n))

def Spec.param(+seg: String) -> J.Json:
  J.JObj{J.JField{"name", J.JStr{Spec.param.name(seg)},
    J.JField{"in", J.JStr{"path"},
      J.JField{"required", J.JBool{True{}},
        J.JField{"schema", Spec.type("string"), J.JNil{}}}}}}

def Spec.param.pick(hit: Bool, +seg: String, rest: J.Json) -> J.Json:
  match hit:
    case True{}:
      J.JCons{Spec.param(seg), rest}
    case False{}:
      rest

def Spec.params.go(segs: List<&2, String>) -> J.Json:
  match segs:
    case Nil{}:
      J.JNil{}
    case Con{+seg, rest}:
      Spec.param.pick(A.Path.is_param(seg), seg, Spec.params.go(rest))

def Spec.params.field(ps: J.Json, rest: J.Json) -> J.Json:
  match ps:
    case J.JNil{}:
      rest
    case other:
      J.JField{"parameters", J.JArr{other}, rest}

# The path's parameters, if it has any, then the request body, if it takes one.
def Spec.params(path: String, rest: J.Json) -> J.Json:
  Spec.params.field(Spec.params.go(String.split(path, J.Text.char(47n))), rest)

def Spec.request(b: Maybe<&2, S.Schema>, rest: J.Json) -> J.Json:
  match b:
    case None{}:
      rest
    case Some{s}:
      J.JField{"requestBody", J.JObj{J.JField{"required", J.JBool{True{}}, J.JField{"content", Spec.content(s), J.JNil{}}}}, rest}

def Spec.scheme(name: String) -> J.Json:
  J.JArr{J.JCons{Spec.obj1(name, J.JArr{J.JNil{}}), J.JNil{}}}

# The key a route needs. An open route lists no scheme, so it needs none.
def Spec.security(u: A.Auth) -> J.Json:
  match u:
    case A.Open{}:
      J.JArr{J.JNil{}}
    case A.Dealers{}:
      Spec.scheme("dealerKey")
    case A.Admins{}:
      Spec.scheme("adminKey")

def Spec.operation(r: A.Route) -> J.Json:
  match r:
    case A.Route{m, p, i, sum, b, w, +u, as}:
      J.JObj{J.JField{"operationId", J.JStr{i},
        J.JField{"summary", J.JStr{sum},
          J.JField{"security", Spec.security(u),
            Spec.params(p, Spec.request(b,
              J.JField{"responses", J.JObj{Spec.responses(w, u, as)}, J.JNil{}}))}}}}

def Spec.method.pick(same: Bool, +r: A.Route, rest: J.Json) -> J.Json:
  match same:
    case True{}:
      J.JField{A.Method.key(A.Route.method(r)), Spec.operation(r), rest}
    case False{}:
      rest

# The operations under one path.
def Spec.methods(+path: String, routes: List<&2, A.Route>) -> J.Json:
  match routes:
    case Nil{}:
      J.JNil{}
    case Con{+r, rest}:
      Spec.method.pick(J.Text.same(path, A.Route.path(r)), r, Spec.methods(path, rest))

def Spec.has(+p: String, xs: List<&2, String>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{x, rest}:
      J.Text.same(p, x) || Spec.has(p, rest)

def Spec.addpath(known: Bool, p: String, seen: List<&2, String>) -> List<&2, String>:
  match known:
    case True{}:
      seen
    case False{}:
      List.append(&2, String, seen, [p])

# Each path once, in the table's order.
def Spec.paths(routes: List<&2, A.Route>, +seen: List<&2, String>) -> List<&2, String>:
  match routes:
    case Nil{}:
      seen
    case Con{+r, rest}:
      Spec.paths(rest, Spec.addpath(Spec.has(A.Route.path(r), seen), A.Route.path(r), seen))

def Spec.items(ps: List<&2, String>, +routes: List<&2, A.Route>) -> J.Json:
  match ps:
    case Nil{}:
      J.JNil{}
    case Con{+p, rest}:
      J.JField{p, J.JObj{Spec.methods(p, routes)}, Spec.items(rest, routes)}

# The document
# ------------

def Spec.bearer(d: String) -> J.Json:
  J.JObj{J.JField{"type", J.JStr{"http"}, J.JField{"scheme", J.JStr{"bearer"}, J.JField{"description", J.JStr{d}, J.JNil{}}}}}

# Both kinds of key go in an Authorization: Bearer header. A missing or
# unknown key gets a 401, and a key for the other kind of route a 403.
def Spec.schemes() -> J.Json:
  J.JObj{J.JField{"dealerKey", Spec.bearer("A dealer organization's API key, issued when an admin adds the organization. It reaches only that organization's appraisals"),
    J.JField{"adminKey", Spec.bearer("The admin key, set as CLOVERLEAF_ADMIN_KEY in the web process's environment"), J.JNil{}}}}

def Spec.doc(+routes: List<&2, A.Route>) -> J.Json:
  J.JObj{J.JField{"openapi", J.JStr{"3.1.0"},
    J.JField{"info", J.JObj{J.JField{"title", J.JStr{"Cloverleaf API"}, J.JField{"version", J.JStr{"0.1.0"}, J.JNil{}}}},
      J.JField{"paths", J.JObj{Spec.items(Spec.paths(routes, []), routes)},
        J.JField{"components", J.JObj{J.JField{"schemas", J.JObj{Spec.components(Spec.unique(Spec.all(routes), []))},
          J.JField{"securitySchemes", Spec.schemes(), J.JNil{}}}}, J.JNil{}}}}}}

def Spec.text() -> String:
  J.Json.pretty(Spec.doc(A.Api.routes(A.Api.ops())), 0n, "")
