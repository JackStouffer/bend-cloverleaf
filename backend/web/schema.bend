import Base

import ./json.bend as J

# API schemas as Bend data. Value(s) is the Bend type a schema describes, so a
# handler's result type comes from its route, and encode and decode are driven
# by the schema. The OpenAPI generator reads the same values.
#
# Rows and list items live inside Schema for the same reason Json's chains do:
# one def can then walk any schema without mutual recursion. An object is
# SObj{name, row}, where the row is a chain of SField and SOpt ending in SEnd.
# A list is SList{SItems{item}}. Build them with Schema.obj and Schema.list.
# An enum is SEnum{name, values}, a string that must be one of its values.
type Schema is Data:
  SStr{}
  SEnum{name: String, values: List<&2, String>}
  SNat{}
  SBool{}
  SList{items: Schema}
  SItems{item: Schema}
  SObj{name: String, row: Schema}
  SField{key: String, value: Schema, rest: Schema}
  SOpt{key: String, value: Schema, rest: Schema}
  SEnd{}

def Schema.list(item: Schema) -> Schema:
  SList{SItems{item}}

def Schema.obj(name: String, row: Schema) -> Schema:
  SObj{name, row}

# An enum's value says which of its names it is: Done for the first name, and
# Fail for one of the rest. So a value is always one of the names, and an enum
# with no names has no values at all.
def Tag(vs: List<&2, String>) -> Data:
  match vs:
    case Nil{}:
      Empty
    case Con{v, rest}:
      Result<&2, &2, Tag(rest), Unit>

def Tag.name(vs: List<&2, String>, t: Tag(vs)) -> String:
  match vs:
    case Nil{}:
      Empty.absurd(String, t)
    case Con{v, rest}:
      match t:
        case Done{u}:
          v
        case Fail{x}:
          Tag.name(rest, x)

def Tag.shift(-rest: List<&2, String>, m: Maybe<&2, Tag(rest)>) -> Maybe<&2, Result<&2, &2, Tag(rest), Unit>>:
  match m:
    case None{}:
      None{}
    case Some{x}:
      Some{Fail{x}}

def Tag.pick(-rest: List<&2, String>, hit: Bool, later: Maybe<&2, Tag(rest)>) -> Maybe<&2, Result<&2, &2, Tag(rest), Unit>>:
  match hit:
    case True{}:
      Some{Done{Unit{}}}
    case False{}:
      Tag.shift(rest, later)

# The first of vs named s, or None.
def Tag.read(vs: List<&2, String>, +s: String) -> Maybe<&2, Tag(vs)>:
  match vs:
    case Nil{}:
      None{}
    case Con{v, +rest}:
      Tag.pick(rest, J.Text.same(s, v), Tag.read(rest, s))

# No name in vs is v.
def Tags.fresh(+v: String, vs: List<&2, String>) -> Bool:
  match vs:
    case Nil{}:
      True{}
    case Con{y, ys}:
      Bool.not(J.Text.same(y, v)) && Tags.fresh(v, ys)

def Tags.distinct(vs: List<&2, String>) -> Bool:
  match vs:
    case Nil{}:
      True{}
    case Con{+v, +rest}:
      Tags.fresh(v, rest) && Tags.distinct(rest)

def Tags.same(a: List<&2, String>, b: List<&2, String>) -> Bool:
  match a b:
    case Nil{} Nil{}:
      True{}
    case Con{x, xs} Con{y, ys}:
      J.Text.same(x, y) && Tags.same(xs, ys)
    case _ _:
      False{}

# Field values come as nested pairs in the row's order, ending in Unit, and an
# optional field's value is a Maybe.
def Value(s: Schema) -> Data:
  match s:
    case SStr{}:
      String
    case SEnum{n, vs}:
      Tag(vs)
    case SNat{}:
      Nat
    case SBool{}:
      Bool
    case SList{it}:
      Value(it)
    case SItems{i}:
      List<&2, Value(i)>
    case SObj{n, r}:
      Value(r)
    case SField{k, f, r}:
      Sigma<&2, &2, Value(f), _ => Value(r)>
    case SOpt{k, f, r}:
      Sigma<&2, &2, Maybe<&2, Value(f)>, _ => Value(r)>
    case SEnd{}:
      Unit

# Encoding
# --------

# Fields come out in the row's order, and a missing optional field is left out.
def encode(s: Schema, v: Value(s)) -> J.Json:
  match s:
    case SStr{}:
      J.JStr{v}
    case SEnum{n, vs}:
      J.JStr{Tag.name(vs, v)}
    case SNat{}:
      J.JNum{v}
    case SBool{}:
      J.JBool{v}
    case SList{it}:
      J.JArr{encode(it, v)}
    case SItems{+i}:
      match v:
        case Nil{}:
          J.JNil{}
        case Con{x, rest}:
          J.JCons{encode(i, x), encode(SItems{i}, rest)}
    case SObj{n, r}:
      J.JObj{encode(r, v)}
    case SField{k, f, r}:
      (a, b) = v
      J.JField{k, encode(f, a), encode(r, b)}
    case SOpt{k, f, r}:
      (m, b) = v
      match m:
        case None{}:
          encode(r, b)
        case Some{a}:
          J.JField{k, encode(f, a), encode(r, b)}
    case SEnd{}:
      J.JNil{}

# Looking up fields
# -----------------

# Whether an object's fields hold key k.
def Take.has(+k: String, j: J.Json) -> Bool:
  match j:
    case J.JField{key, v, t}:
      J.Text.same(k, key) || Take.has(k, t)
    case other:
      False{}

def Take.found.pick(same: Bool, v: J.Json, found: J.Json) -> J.Json:
  match same:
    case True{}:
      v
    case False{}:
      found

# The first value under key k. A missing key reads as JNil, which no value
# schema accepts.
def Take.found(+k: String, j: J.Json) -> J.Json:
  match j:
    case J.JField{key, v, t}:
      Take.found.pick(J.Text.same(k, key), v, Take.found(k, t))
    case other:
      J.JNil{}

def Take.rest.pick(same: Bool, key: String, v: J.Json, t: J.Json, rest: J.Json) -> J.Json:
  match same:
    case True{}:
      t
    case False{}:
      J.JField{key, v, rest}

# The fields with the first one under key k taken out. Each field of a row takes
# its key out, so a key the row doesn't name is left over, and a repeated key
# leaves its second copy over. SEnd refuses anything left over.
def Take.rest(+k: String, j: J.Json) -> J.Json:
  match j:
    case J.JField{+key, +v, +t}:
      Take.rest.pick(J.Text.same(k, key), key, v, t, Take.rest(k, t))
    case other:
      other

# Decoding
# --------

def Codec.both(-A: Data, -B: Data, a: Maybe<&2, A>, b: Maybe<&2, B>) -> Maybe<&2, Sigma<&2, &2, A, _ => B>>:
  match a b:
    case Some{x} Some{y}:
      Some{(x, y)}
    case _ _:
      None{}

def Codec.cons(-A: Data, a: Maybe<&2, A>, b: Maybe<&2, List<&2, A>>) -> Maybe<&2, List<&2, A>>:
  match a b:
    case Some{x} Some{xs}:
      Some{x <> xs}
    case _ _:
      None{}

# A missing optional field is None. A present one has to decode.
def Codec.opt(-A: Data, present: Bool, a: Maybe<&2, A>) -> Maybe<&2, Maybe<&2, A>>:
  match present a:
    case False{} _:
      Some{None{}}
    case True{} Some{x}:
      Some{Some{x}}
    case True{} None{}:
      None{}

def Codec.end(j: J.Json) -> Maybe<&2, Unit>:
  match j:
    case J.JNil{}:
      Some{Unit{}}
    case other:
      None{}

def Codec.str(j: J.Json) -> Maybe<&2, String>:
  match j:
    case J.JStr{v}:
      Some{v}
    case other:
      None{}

def Codec.tag(vs: List<&2, String>, m: Maybe<&2, String>) -> Maybe<&2, Tag(vs)>:
  match m:
    case None{}:
      None{}
    case Some{s}:
      Tag.read(vs, s)

def Codec.nat.pick(ok: Bool, n: Nat) -> Maybe<&2, Nat>:
  match ok:
    case True{}:
      Some{n}
    case False{}:
      None{}

# A number above Json.Max is refused, as the parser and the spec refuse it.
def Codec.nat(j: J.Json) -> Maybe<&2, Nat>:
  match j:
    case J.JNum{+v}:
      Codec.nat.pick(J.Json.small(v), v)
    case other:
      None{}

def Codec.bool(j: J.Json) -> Maybe<&2, Bool>:
  match j:
    case J.JBool{v}:
      Some{v}
    case other:
      None{}

# The value a schema reads from JSON, or None. Objects are strict: a missing
# required field, an unknown field and a repeated field are all refused.
def decode(s: Schema, +j: J.Json) -> Maybe<&2, Value(s)>:
  match s:
    case SStr{}:
      Codec.str(j)
    case SEnum{n, vs}:
      Codec.tag(vs, Codec.str(j))
    case SNat{}:
      Codec.nat(j)
    case SBool{}:
      Codec.bool(j)
    case SList{it}:
      match j:
        case J.JArr{xs}:
          decode(it, xs)
        case other:
          None{}
    case SItems{+i}:
      match j:
        case J.JNil{}:
          Some{[]}
        case J.JCons{h, t}:
          Codec.cons(Value(i), decode(i, h), decode(SItems{i}, t))
        case other:
          None{}
    case SObj{n, r}:
      match j:
        case J.JObj{fs}:
          decode(r, fs)
        case other:
          None{}
    case SField{+k, f, r}:
      Codec.both(Value(f), Value(r), decode(f, Take.found(k, j)), decode(r, Take.rest(k, j)))
    case SOpt{+k, f, r}:
      Codec.both(Maybe<&2, Value(f)>, Value(r), Codec.opt(Value(f), Take.has(k, j), decode(f, Take.found(k, j))), decode(r, Take.rest(k, j)))
    case SEnd{}:
      Codec.end(j)

# Numbers in range
# ----------------

# Every Nat in v is at most Json.Max, the largest number the parser reads and
# the maximum the spec publishes. A Nat can be larger, so encode alone could
# send a number no client is told to expect. The laws ask for this of every
# value they encode, and every handler's reply is checked for it.
def Schema.within(s: Schema, v: Value(s)) -> Bool:
  match s:
    case SNat{}:
      J.Json.small(v)
    case SList{it}:
      Schema.within(it, v)
    case SItems{+i}:
      match v:
        case Nil{}:
          True{}
        case Con{x, rest}:
          Schema.within(i, x) && Schema.within(SItems{i}, rest)
    case SObj{n, r}:
      Schema.within(r, v)
    case SField{k, f, r}:
      (a, b) = v
      Schema.within(f, a) && Schema.within(r, b)
    case SOpt{k, f, r}:
      (m, b) = v
      match m:
        case None{}:
          Schema.within(r, b)
        case Some{a}:
          Schema.within(f, a) && Schema.within(r, b)
    case other:
      True{}

# No number anywhere in s, so every value of s is within range.
def Schema.free(s: Schema) -> Bool:
  match s:
    case SNat{}:
      False{}
    case SList{it}:
      Schema.free(it)
    case SItems{i}:
      Schema.free(i)
    case SObj{n, r}:
      Schema.free(r)
    case SField{k, f, r}:
      Schema.free(f) && Schema.free(r)
    case SOpt{k, f, r}:
      Schema.free(f) && Schema.free(r)
    case other:
      True{}

# Well-formed keys
# ----------------

# No field of the row s is named k.
def Schema.fresh(+k: String, s: Schema) -> Bool:
  match s:
    case SField{key, f, r}:
      Bool.not(J.Text.same(k, key)) && Schema.fresh(k, r)
    case SOpt{key, f, r}:
      Bool.not(J.Text.same(k, key)) && Schema.fresh(k, r)
    case other:
      True{}

# No object in s names a field twice. JSON can't hold one object with a key
# twice, so the round-trip law needs this, and every schema in the route table
# is checked for it.
def Schema.distinct(s: Schema) -> Bool:
  match s:
    case SList{it}:
      Schema.distinct(it)
    case SItems{i}:
      Schema.distinct(i)
    case SEnum{n, vs}:
      Tags.distinct(vs)
    case SObj{n, r}:
      Schema.distinct(r)
    case SField{+k, f, +r}:
      Schema.distinct(f) && Schema.fresh(k, r) && Schema.distinct(r)
    case SOpt{+k, f, +r}:
      Schema.distinct(f) && Schema.fresh(k, r) && Schema.distinct(r)
    case other:
      True{}

# Well-formed shapes
# ------------------

# Where a schema sits: as a value, as a list's items, or as an object's row.
type Spot is Data:
  AtValue{}
  AtItems{}
  AtRow{}

# Whether s has the shape its spot needs. Items only go inside a list, rows only
# inside an object, every field holds a value, and an enum has a name.
def Schema.fits(s: Schema, at: Spot) -> Bool:
  match s at:
    case SStr{} AtValue{}:
      True{}
    case SEnum{n, Con{v, rest}} AtValue{}:
      True{}
    case SNat{} AtValue{}:
      True{}
    case SBool{} AtValue{}:
      True{}
    case SList{it} AtValue{}:
      Schema.fits(it, AtItems{})
    case SItems{i} AtItems{}:
      Schema.fits(i, AtValue{})
    case SObj{n, r} AtValue{}:
      Schema.fits(r, AtRow{})
    case SField{k, f, r} AtRow{}:
      Schema.fits(f, AtValue{}) && Schema.fits(r, AtRow{})
    case SOpt{k, f, r} AtRow{}:
      Schema.fits(f, AtValue{}) && Schema.fits(r, AtRow{})
    case SEnd{} AtRow{}:
      True{}
    case _ _:
      False{}

# A schema a route can use. A missing key reads as JNil, and only items and
# rows accept JNil, so this is what makes a required field required. Every
# schema in the route table is checked for it.
def Schema.wellformed(s: Schema) -> Bool:
  Schema.fits(s, AtValue{})

# Structural equality, so the spec generator can tell two definitions of one
# name apart.
def Schema.same(a: Schema, b: Schema) -> Bool:
  match a b:
    case SStr{} SStr{}:
      True{}
    case SEnum{n, xs} SEnum{m, ys}:
      J.Text.same(n, m) && Tags.same(xs, ys)
    case SNat{} SNat{}:
      True{}
    case SBool{} SBool{}:
      True{}
    case SList{x} SList{y}:
      Schema.same(x, y)
    case SItems{x} SItems{y}:
      Schema.same(x, y)
    case SObj{n, x} SObj{m, y}:
      J.Text.same(n, m) && Schema.same(x, y)
    case SField{k, f, r} SField{l, g, q}:
      J.Text.same(k, l) && Schema.same(f, g) && Schema.same(r, q)
    case SOpt{k, f, r} SOpt{l, g, q}:
      J.Text.same(k, l) && Schema.same(f, g) && Schema.same(r, q)
    case SEnd{} SEnd{}:
      True{}
    case _ _:
      False{}
