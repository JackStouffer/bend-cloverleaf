import Base
import ../web/json.bend as J
import ../web/schema.bend as S
import ../web/api.bend as A
import ./logic.bend as L

# Lemmas behind the codec laws.

law same_refl:
  for +s: String
  {J.Text.same(s, s) == True{} : Bool}

def same_refl(s):
  match s:
    case SNil{}:
      {==}
    case SCon{c, t}:
      L.and_i(Nat.is_eq(J.Text.code(c), J.Text.code(c)), J.Text.same(t, t), L.eq_refl(J.Text.code(c)), same_refl(t))

def MJ() -> Data:
  Maybe<&2, J.Json>

law found_hit:
  for +k: String
  for +v: J.Json
  for +t: J.Json
  {S.Take.found(k, J.JField{k, v, t}) == v : J.Json}

def found_hit(k, v, t):
  %Equal.sym(Bool, J.Text.same(k, k), True{}, same_refl(k)) : {S.Take.found.pick(_, v, S.Take.found(k, t)) == v : J.Json}
  {==}

law rest_hit:
  for +k: String
  for +v: J.Json
  for +t: J.Json
  {S.Take.rest(k, J.JField{k, v, t}) == t : J.Json}

def rest_hit(k, v, t):
  %Equal.sym(Bool, J.Text.same(k, k), True{}, same_refl(k)) : {S.Take.rest.pick(_, k, v, t, S.Take.rest(k, t)) == t : J.Json}
  {==}

law has_hit:
  for +k: String
  for +v: J.Json
  for +t: J.Json
  {S.Take.has(k, J.JField{k, v, t}) == True{} : Bool}

def has_hit(k, v, t):
  %Equal.sym(Bool, J.Text.same(k, k), True{}, same_refl(k)) : {Bool.or(_, S.Take.has(k, t)) == True{} : Bool}
  {==}

law not_t:
  for +b: Bool
  for e: {Bool.not(b) == True{} : Bool}
  {b == False{} : Bool}

def not_t(b, e):
  match b:
    case True{}:
      L.never({True{} == False{} : Bool}, e)
    case False{}:
      {==}

# A key the row doesn't name is never found in the row's encoding, and taking
# it out leaves the encoding as it was.
law has_miss:
  for +k: String
  for +r: S.Schema
  for +b: S.Value(r)
  for +e: {S.Schema.fresh(k, r) == True{} : Bool}
  {S.Take.has(k, S.encode(r, b)) == False{} : Bool}

def has_miss(k, r, b, e):
  match r:
    case S.SStr{}:
      {==}
    case S.SNat{}:
      {==}
    case S.SBool{}:
      {==}
    case S.SList{it}:
      {==}
    case S.SItems{i}:
      match b:
        case Nil{}:
          {==}
        case Con{x, rest}:
          {==}
    case S.SObj{n, q}:
      {==}
    case S.SField{key, f, q}:
      match b:
        case (b1, b2):
          %Equal.sym(Bool, J.Text.same(k, key), False{}, not_t(J.Text.same(k, key), L.and_l(Bool.not(J.Text.same(k, key)), S.Schema.fresh(k, q), e))) : {Bool.or(_, S.Take.has(k, S.encode(q, b2))) == False{} : Bool}
          has_miss(k, q, b2, L.and_r(Bool.not(J.Text.same(k, key)), S.Schema.fresh(k, q), e))
    case S.SOpt{key, f, q}:
      match b:
        case (m, b2):
          match m:
            case None{}:
              has_miss(k, q, b2, L.and_r(Bool.not(J.Text.same(k, key)), S.Schema.fresh(k, q), e))
            case Some{a}:
              %Equal.sym(Bool, J.Text.same(k, key), False{}, not_t(J.Text.same(k, key), L.and_l(Bool.not(J.Text.same(k, key)), S.Schema.fresh(k, q), e))) : {Bool.or(_, S.Take.has(k, S.encode(q, b2))) == False{} : Bool}
              has_miss(k, q, b2, L.and_r(Bool.not(J.Text.same(k, key)), S.Schema.fresh(k, q), e))
    case S.SEnd{}:
      {==}

law rest_miss:
  for +k: String
  for +r: S.Schema
  for +b: S.Value(r)
  for +e: {S.Schema.fresh(k, r) == True{} : Bool}
  {S.Take.rest(k, S.encode(r, b)) == S.encode(r, b) : J.Json}

def rest_miss(k, r, b, e):
  match r:
    case S.SStr{}:
      {==}
    case S.SNat{}:
      {==}
    case S.SBool{}:
      {==}
    case S.SList{it}:
      {==}
    case S.SItems{i}:
      match b:
        case Nil{}:
          {==}
        case Con{x, rest}:
          {==}
    case S.SObj{n, q}:
      {==}
    case S.SField{key, f, q}:
      match b:
        case (b1, b2):
          %Equal.sym(Bool, J.Text.same(k, key), False{}, not_t(J.Text.same(k, key), L.and_l(Bool.not(J.Text.same(k, key)), S.Schema.fresh(k, q), e))) : {S.Take.rest.pick(_, key, S.encode(f, b1), S.encode(q, b2), S.Take.rest(k, S.encode(q, b2))) == J.JField{key, S.encode(f, b1), S.encode(q, b2)} : J.Json}
          %Equal.sym(J.Json, S.Take.rest(k, S.encode(q, b2)), S.encode(q, b2), rest_miss(k, q, b2, L.and_r(Bool.not(J.Text.same(k, key)), S.Schema.fresh(k, q), e))) : {J.JField{key, S.encode(f, b1), _} == J.JField{key, S.encode(f, b1), S.encode(q, b2)} : J.Json}
          {==}
    case S.SOpt{key, f, q}:
      match b:
        case (m, b2):
          match m:
            case None{}:
              rest_miss(k, q, b2, L.and_r(Bool.not(J.Text.same(k, key)), S.Schema.fresh(k, q), e))
            case Some{a}:
              %Equal.sym(Bool, J.Text.same(k, key), False{}, not_t(J.Text.same(k, key), L.and_l(Bool.not(J.Text.same(k, key)), S.Schema.fresh(k, q), e))) : {S.Take.rest.pick(_, key, S.encode(f, a), S.encode(q, b2), S.Take.rest(k, S.encode(q, b2))) == J.JField{key, S.encode(f, a), S.encode(q, b2)} : J.Json}
              %Equal.sym(J.Json, S.Take.rest(k, S.encode(q, b2)), S.encode(q, b2), rest_miss(k, q, b2, L.and_r(Bool.not(J.Text.same(k, key)), S.Schema.fresh(k, q), e))) : {J.JField{key, S.encode(f, a), _} == J.JField{key, S.encode(f, a), S.encode(q, b2)} : J.Json}
              {==}
    case S.SEnd{}:
      {==}

def MV(s: S.Schema) -> Data:
  Maybe<&2, S.Value(s)>

law roundtrip:
  for +s: S.Schema
  for +v: S.Value(s)
  for +e: {S.Schema.distinct(s) == True{} : Bool}
  {S.decode(s, S.encode(s, v)) == Some{v} : MV(s)}

def roundtrip(s, v, e):
  match s:
    case S.SStr{}:
      {==}
    case S.SNat{}:
      {==}
    case S.SBool{}:
      {==}
    case S.SList{it}:
      roundtrip(it, v, e)
    case S.SItems{i}:
      match v:
        case Nil{}:
          {==}
        case Con{x, rest}:
          %Equal.sym(MV(i), S.decode(i, S.encode(i, x)), Some{x}, roundtrip(i, x, e)) : {S.Codec.cons(S.Value(i), _, S.decode(S.SItems{i}, S.encode(S.SItems{i}, rest))) == Some{x <> rest} : MV(S.SItems{i})}
          %Equal.sym(MV(S.SItems{i}), S.decode(S.SItems{i}, S.encode(S.SItems{i}, rest)), Some{rest}, roundtrip(S.SItems{i}, rest, e)) : {S.Codec.cons(S.Value(i), Some{x}, _) == Some{x <> rest} : MV(S.SItems{i})}
          {==}
    case S.SObj{n, r}:
      roundtrip(r, v, e)
    case S.SField{k, f, r}:
      match v:
        case (a, b):
          %Equal.sym(J.Json, S.Take.found(k, J.JField{k, S.encode(f, a), S.encode(r, b)}), S.encode(f, a), found_hit(k, S.encode(f, a), S.encode(r, b))) : {S.Codec.both(S.Value(f), S.Value(r), S.decode(f, _), S.decode(r, S.Take.rest(k, J.JField{k, S.encode(f, a), S.encode(r, b)}))) == Some{(a, b)} : MV(S.SField{k, f, r})}
          %Equal.sym(J.Json, S.Take.rest(k, J.JField{k, S.encode(f, a), S.encode(r, b)}), S.encode(r, b), rest_hit(k, S.encode(f, a), S.encode(r, b))) : {S.Codec.both(S.Value(f), S.Value(r), S.decode(f, S.encode(f, a)), S.decode(r, _)) == Some{(a, b)} : MV(S.SField{k, f, r})}
          %Equal.sym(MV(f), S.decode(f, S.encode(f, a)), Some{a}, roundtrip(f, a, L.and_l(S.Schema.distinct(f), S.Schema.fresh(k, r), L.and_l(Bool.and(S.Schema.distinct(f), S.Schema.fresh(k, r)), S.Schema.distinct(r), e)))) : {S.Codec.both(S.Value(f), S.Value(r), _, S.decode(r, S.encode(r, b))) == Some{(a, b)} : MV(S.SField{k, f, r})}
          %Equal.sym(MV(r), S.decode(r, S.encode(r, b)), Some{b}, roundtrip(r, b, L.and_r(Bool.and(S.Schema.distinct(f), S.Schema.fresh(k, r)), S.Schema.distinct(r), e))) : {S.Codec.both(S.Value(f), S.Value(r), Some{a}, _) == Some{(a, b)} : MV(S.SField{k, f, r})}
          {==}
    case S.SOpt{k, f, r}:
      match v:
        case (m, b):
          match m:
            case None{}:
              %Equal.sym(Bool, S.Take.has(k, S.encode(r, b)), False{}, has_miss(k, r, b, L.and_r(S.Schema.distinct(f), S.Schema.fresh(k, r), L.and_l(Bool.and(S.Schema.distinct(f), S.Schema.fresh(k, r)), S.Schema.distinct(r), e)))) : {S.Codec.both(Maybe<&2, S.Value(f)>, S.Value(r), S.Codec.opt(S.Value(f), _, S.decode(f, S.Take.found(k, S.encode(r, b)))), S.decode(r, S.Take.rest(k, S.encode(r, b)))) == Some{(None{}, b)} : MV(S.SOpt{k, f, r})}
              %Equal.sym(J.Json, S.Take.rest(k, S.encode(r, b)), S.encode(r, b), rest_miss(k, r, b, L.and_r(S.Schema.distinct(f), S.Schema.fresh(k, r), L.and_l(Bool.and(S.Schema.distinct(f), S.Schema.fresh(k, r)), S.Schema.distinct(r), e)))) : {S.Codec.both(Maybe<&2, S.Value(f)>, S.Value(r), S.Codec.opt(S.Value(f), False{}, S.decode(f, S.Take.found(k, S.encode(r, b)))), S.decode(r, _)) == Some{(None{}, b)} : MV(S.SOpt{k, f, r})}
              %Equal.sym(MV(r), S.decode(r, S.encode(r, b)), Some{b}, roundtrip(r, b, L.and_r(Bool.and(S.Schema.distinct(f), S.Schema.fresh(k, r)), S.Schema.distinct(r), e))) : {S.Codec.both(Maybe<&2, S.Value(f)>, S.Value(r), Some{None{}}, _) == Some{(None{}, b)} : MV(S.SOpt{k, f, r})}
              {==}
            case Some{a}:
              %Equal.sym(Bool, S.Take.has(k, J.JField{k, S.encode(f, a), S.encode(r, b)}), True{}, has_hit(k, S.encode(f, a), S.encode(r, b))) : {S.Codec.both(Maybe<&2, S.Value(f)>, S.Value(r), S.Codec.opt(S.Value(f), _, S.decode(f, S.Take.found(k, J.JField{k, S.encode(f, a), S.encode(r, b)}))), S.decode(r, S.Take.rest(k, J.JField{k, S.encode(f, a), S.encode(r, b)}))) == Some{(Some{a}, b)} : MV(S.SOpt{k, f, r})}
              %Equal.sym(J.Json, S.Take.found(k, J.JField{k, S.encode(f, a), S.encode(r, b)}), S.encode(f, a), found_hit(k, S.encode(f, a), S.encode(r, b))) : {S.Codec.both(Maybe<&2, S.Value(f)>, S.Value(r), S.Codec.opt(S.Value(f), True{}, S.decode(f, _)), S.decode(r, S.Take.rest(k, J.JField{k, S.encode(f, a), S.encode(r, b)}))) == Some{(Some{a}, b)} : MV(S.SOpt{k, f, r})}
              %Equal.sym(J.Json, S.Take.rest(k, J.JField{k, S.encode(f, a), S.encode(r, b)}), S.encode(r, b), rest_hit(k, S.encode(f, a), S.encode(r, b))) : {S.Codec.both(Maybe<&2, S.Value(f)>, S.Value(r), S.Codec.opt(S.Value(f), True{}, S.decode(f, S.encode(f, a))), S.decode(r, _)) == Some{(Some{a}, b)} : MV(S.SOpt{k, f, r})}
              %Equal.sym(MV(f), S.decode(f, S.encode(f, a)), Some{a}, roundtrip(f, a, L.and_l(S.Schema.distinct(f), S.Schema.fresh(k, r), L.and_l(Bool.and(S.Schema.distinct(f), S.Schema.fresh(k, r)), S.Schema.distinct(r), e)))) : {S.Codec.both(Maybe<&2, S.Value(f)>, S.Value(r), S.Codec.opt(S.Value(f), True{}, _), S.decode(r, S.encode(r, b))) == Some{(Some{a}, b)} : MV(S.SOpt{k, f, r})}
              %Equal.sym(MV(r), S.decode(r, S.encode(r, b)), Some{b}, roundtrip(r, b, L.and_r(Bool.and(S.Schema.distinct(f), S.Schema.fresh(k, r)), S.Schema.distinct(r), e))) : {S.Codec.both(Maybe<&2, S.Value(f)>, S.Value(r), Some{Some{a}}, _) == Some{(Some{a}, b)} : MV(S.SOpt{k, f, r})}
              {==}
    case S.SEnd{}:
      match v:
        case Unit{}:
          {==}

# Every reply a handler can build is accepted by its own route's answers: the
# status is the answer's, and the body decodes under the answer's schema.
law reply_fits:
  for +as: List<&2, A.Answer>
  for +r: A.Reply(as)
  for +e: {A.Answers.distinct(as) == True{} : Bool}
  {A.Answers.accepts(as, A.Reply.status(as, r), A.Reply.body(as, r)) == True{} : Bool}

def reply_fits(as, r, e):
  match as:
    case Nil{}:
      Empty.absurd({False{} == True{} : Bool}, r)
    case Con{A.Answer{st, d, s}, rest}:
      match r:
        case Done{v}:
          %Equal.sym(Bool, Nat.is_eq(st, st), True{}, L.eq_refl(st)) : {Bool.or(Bool.and(_, Maybe.is_some(&2, S.Value(s), S.decode(s, S.encode(s, v)))), A.Answers.accepts(rest, st, S.encode(s, v))) == True{} : Bool}
          %Equal.sym(MV(s), S.decode(s, S.encode(s, v)), Some{v}, roundtrip(s, v, L.and_l(S.Schema.distinct(s), A.Answers.distinct(rest), e))) : {Bool.or(Bool.and(True{}, Maybe.is_some(&2, S.Value(s), _)), A.Answers.accepts(rest, st, S.encode(s, v))) == True{} : Bool}
          {==}
        case Fail{x}:
          L.or_right(Bool.and(Nat.is_eq(st, A.Reply.status(rest, x)), Maybe.is_some(&2, S.Value(s), S.decode(s, A.Reply.body(rest, x)))),
            A.Answers.accepts(rest, A.Reply.status(rest, x), A.Reply.body(rest, x)),
            reply_fits(rest, x, L.and_r(S.Schema.distinct(s), A.Answers.distinct(rest), e)))
