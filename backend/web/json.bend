import Base

# JSON as a tree, with a printer and a parser. Pure, so the web process and the
# spec generator share it, and the laws can reason about it.
#
# Arrays and objects hold their members as chains inside Json itself, not as a
# List of Json. A def over Json can then reach every member by matching, with
# no helper over the List calling back into it, which would be mutual recursion.
# JArr holds a chain of JCons ending in JNil, and JObj a chain of JField ending
# in JNil. The printer treats any other shape inside them as a chain's end.
#
# Numbers are Nat only, because every number in the domain is a Nat. The parser
# refuses fractions, exponents, signs and more than Json.Digits() digits, so a
# number from outside never reaches Nat's 2^48 trap.
type Json is Data:
  JNull{}
  JBool{value: Bool}
  JNum{value: Nat}
  JStr{value: String}
  JArr{items: Json}
  JObj{fields: Json}
  JNil{}
  JCons{head: Json, tail: Json}
  JField{key: String, value: Json, tail: Json}

# 99,999,999,999,999 is the largest number the parser reads, well under 2^48.
def Json.Digits() -> Nat:
  14n

def Json.Max() -> Nat:
  Nat.sub(Nat.mul(100000000n, 1000000n), 1n)

# Whether n has at most Json.Digits() digits, so is at most Json.Max. Checked
# by its digits and not against Json.Max, because the checker unfolds a
# comparison with a 14-digit literal one step per unit and runs out of stack.
def Json.small(n: Nat) -> Bool:
  Nat.is_le(String.length(Nat.show(n)), Json.Digits())

# Text
# ----
def Text.code(c: Char) -> Nat:
  U32.to_nat(Char.to_u32(c))

def Text.char(n: Nat) -> Char:
  Chr{U32.from_nat(n)}

# Character equality through Nat, so that its reflexivity is a lemma over Nat
# and needs nothing about U32's bits. Schema keys are compared with this.
def Text.same(a: String, b: String) -> Bool:
  match a b:
    case SNil{} SNil{}:
      True{}
    case SCon{x, at} SCon{y, bt}:
      Nat.is_eq(Text.code(x), Text.code(y)) && Text.same(at, bt)
    case _ _:
      False{}

def Text.width.pick(one: Bool, two: Bool, three: Bool) -> Nat:
  match one two three:
    case True{} _ _:
      1n
    case False{} True{} _:
      2n
    case False{} False{} True{}:
      3n
    case False{} False{} False{}:
      4n

# The UTF-8 length of one code point.
def Text.width(+n: Nat) -> Nat:
  Text.width.pick(Nat.is_lt(n, 128n), Nat.is_lt(n, 2048n), Nat.is_lt(n, 65536n))

# The UTF-8 length of a string, for Content-Length.
def Text.bytes(s: String, acc: Nat) -> Nat:
  match s:
    case SNil{}:
      acc
    case SCon{c, t}:
      Text.bytes(t, Nat.add(acc, Text.width(Text.code(c))))

def Text.hex.pick(digit: Bool, n: Nat) -> Char:
  match digit:
    case True{}:
      Text.char(Nat.add(48n, n))
    case False{}:
      Text.char(Nat.add(87n, n))

def Text.hex(+n: Nat) -> Char:
  Text.hex.pick(Nat.is_lt(n, 10n), n)

def Text.spaces(n: Nat) -> String:
  String.repeat(" ", n)

# The same escapes as JavaScript's JSON.stringify, so the two print the same text.
def Json.escape.control(+n: Nat, acc: String) -> String:
  match n:
    case 8n:
      SCon{'\\', SCon{'b', acc}}
    case 9n:
      SCon{'\\', SCon{'t', acc}}
    case 10n:
      SCon{'\\', SCon{'n', acc}}
    case 12n:
      SCon{'\\', SCon{'f', acc}}
    case 13n:
      SCon{'\\', SCon{'r', acc}}
    case other:
      "\\u00" ++ SCon{Text.hex(Nat.div(n, 16n)), SCon{Text.hex(Nat.mod(n, 16n)), acc}}

# Printing
# --------
def Json.escape.pick(quote: Bool, slash: Bool, control: Bool, +n: Nat, c: Char, acc: String) -> String:
  match quote slash control:
    case True{} _ _:
      SCon{'\\', SCon{'"', acc}}
    case False{} True{} _:
      SCon{'\\', SCon{'\\', acc}}
    case False{} False{} True{}:
      Json.escape.control(n, acc)
    case False{} False{} False{}:
      SCon{c, acc}

# Control characters, quotes and backslashes are escaped. Everything else is
# written as it is, so the output stays valid UTF-8 for any valid input.
def Json.escape.code(+n: Nat, c: Char, acc: String) -> String:
  Json.escape.pick(Nat.is_eq(n, 34n), Nat.is_eq(n, 92n), Nat.is_lt(n, 32n), n, c, acc)

def Json.escape(s: String, acc: String) -> String:
  match s:
    case SNil{}:
      acc
    case SCon{+c, t}:
      Json.escape.code(Text.code(c), c, Json.escape(t, acc))

def Json.quote(s: String, acc: String) -> String:
  SCon{'"', Json.escape(s, SCon{'"', acc})}

def Json.bool(b: Bool) -> String:
  match b:
    case True{}:
      "true"
    case False{}:
      "false"

# A comma comes before every member but the first, which is the same as after
# every member that has another one behind it.
def Json.more(j: Json) -> Bool:
  match j:
    case JCons{h, t}:
      True{}
    case JField{k, v, t}:
      True{}
    case other:
      False{}

def Json.comma(more: Bool, acc: String) -> String:
  match more:
    case True{}:
      SCon{',', acc}
    case False{}:
      acc

# Compact output, with nothing between tokens.
def Json.write(j: Json, acc: String) -> String:
  match j:
    case JNull{}:
      "null" ++ acc
    case JBool{b}:
      Json.bool(b) ++ acc
    case JNum{n}:
      Nat.show(n) ++ acc
    case JStr{s}:
      Json.quote(s, acc)
    case JArr{xs}:
      SCon{'[', Json.write(xs, SCon{']', acc})}
    case JObj{fs}:
      SCon{'{', Json.write(fs, SCon{'}', acc})}
    case JNil{}:
      acc
    case JCons{h, +t}:
      Json.write(h, Json.comma(Json.more(t), Json.write(t, acc)))
    case JField{k, v, +t}:
      Json.quote(k, SCon{':', Json.write(v, Json.comma(Json.more(t), Json.write(t, acc)))})

def Json.print(j: Json) -> String:
  Json.write(j, "")

# Every number in j is at most Json.Max, so the parser reads j's text back.
def Json.fits(j: Json) -> Bool:
  match j:
    case JNum{n}:
      Json.small(n)
    case JArr{xs}:
      Json.fits(xs)
    case JObj{fs}:
      Json.fits(fs)
    case JCons{h, t}:
      Json.fits(h) && Json.fits(t)
    case JField{k, v, t}:
      Json.fits(v) && Json.fits(t)
    case other:
      True{}

def Json.break(more: Bool, acc: String) -> String:
  match more:
    case True{}:
      ",\n" ++ acc
    case False{}:
      acc

# Two-space indented output, for files people read and diff, like openapi.json.
# ind is the indentation of the members when j is a chain, and of j's own
# closing bracket otherwise.
def Json.pretty(j: Json, +ind: Nat, acc: String) -> String:
  match j:
    case JArr{JNil{}}:
      "[]" ++ acc
    case JObj{JNil{}}:
      "{}" ++ acc
    case JArr{xs}:
      "[\n" ++ Json.pretty(xs, Nat.add(ind, 2n), "\n" ++ Text.spaces(ind) ++ SCon{']', acc})
    case JObj{fs}:
      "{\n" ++ Json.pretty(fs, Nat.add(ind, 2n), "\n" ++ Text.spaces(ind) ++ SCon{'}', acc})
    case JCons{h, +t}:
      Text.spaces(ind) ++ Json.pretty(h, ind, Json.break(Json.more(t), Json.pretty(t, ind, acc)))
    case JField{k, v, +t}:
      Text.spaces(ind) ++ Json.quote(k, ": " ++ Json.pretty(v, ind, Json.break(Json.more(t), Json.pretty(t, ind, acc))))
    case JNil{}:
      acc
    case other:
      Json.write(other, acc)

# Building
# --------

type Member is Data:
  Member{key: String, value: Json}

# A chain from members collected in reverse.
def Json.items(rev: List<&2, Json>, acc: Json) -> Json:
  match rev:
    case Nil{}:
      acc
    case Con{x, t}:
      Json.items(t, JCons{x, acc})

def Json.fields(rev: List<&2, Member>, acc: Json) -> Json:
  match rev:
    case Nil{}:
      acc
    case Con{Member{k, v}, t}:
      Json.fields(t, JField{k, v, acc})

def Json.list(xs: List<&2, Json>) -> Json:
  JArr{Json.items(List.reverse(&2, Json, xs), JNil{})}

# Lexing
# ------
type Tok is Data:
  TOpen{}
  TClose{}
  TLeft{}
  TRight{}
  TColon{}
  TComma{}
  TStr{value: String}
  TNum{value: Nat}
  TLit{value: Json}

# What the lexer is in the middle of. buf holds a string's characters in reverse,
# and hex the value and count of the \u digits still to come.
type Lex is Data:
  LTop{}
  LStr{buf: List<&2, Char>}
  LEsc{buf: List<&2, Char>}
  LHex{buf: List<&2, Char>, value: Nat, left: Nat}
  LNum{value: Nat, digits: Nat}
  LWord{rest: String, tok: Tok}

type Lexed is Data:
  Lexed{mode: Lex, out: List<&2, Tok>}

def Lex.go(mode: Lex, out: List<&2, Tok>) -> Maybe<&2, Lexed>:
  Some{Lexed{mode, out}}

def Lex.top.mark(n: Nat, out: List<&2, Tok>) -> Maybe<&2, Lexed>:
  match n:
    case 123n:
      Lex.go(LTop{}, TOpen{} <> out)
    case 125n:
      Lex.go(LTop{}, TClose{} <> out)
    case 91n:
      Lex.go(LTop{}, TLeft{} <> out)
    case 93n:
      Lex.go(LTop{}, TRight{} <> out)
    case 58n:
      Lex.go(LTop{}, TColon{} <> out)
    case 44n:
      Lex.go(LTop{}, TComma{} <> out)
    case 34n:
      Lex.go(LStr{[]}, out)
    case 116n:
      Lex.go(LWord{"rue", TLit{JBool{True{}}}}, out)
    case 102n:
      Lex.go(LWord{"alse", TLit{JBool{False{}}}}, out)
    case 110n:
      Lex.go(LWord{"ull", TLit{JNull{}}}, out)
    case other:
      None{}

def Lex.top.digit(other: Bool, +n: Nat, out: List<&2, Tok>) -> Maybe<&2, Lexed>:
  match other:
    case False{}:
      Lex.go(LNum{Nat.sub(n, 48n), 1n}, out)
    case True{}:
      Lex.top.mark(n, out)

def Lex.top.space(space: Bool, +n: Nat, out: List<&2, Tok>) -> Maybe<&2, Lexed>:
  match space:
    case True{}:
      Lex.go(LTop{}, out)
    case False{}:
      Lex.top.digit(Nat.is_lt(n, 48n) || Nat.is_lt(57n, n), n, out)

def Lex.top.pick(+n: Nat, out: List<&2, Tok>) -> Maybe<&2, Lexed>:
  Lex.top.space(Nat.is_eq(n, 32n) || Nat.is_eq(n, 10n) || Nat.is_eq(n, 13n) || Nat.is_eq(n, 9n), n, out)

def Lex.top(c: Char, out: List<&2, Tok>) -> Maybe<&2, Lexed>:
  Lex.top.pick(Text.code(c), out)

# Surrogate pairs from \u escapes combine into one code point. A lone surrogate
# is refused, since it can't be written as UTF-8.
def Lex.surrogate(+n: Nat) -> Bool:
  Nat.is_le(55296n, n) && Nat.is_lt(n, 57344n)

def Lex.high(+n: Nat) -> Bool:
  Nat.is_le(55296n, n) && Nat.is_lt(n, 56320n)

def Lex.low(+n: Nat) -> Bool:
  Nat.is_le(56320n, n) && Nat.is_lt(n, 57344n)

def Lex.pair(+hi: Nat, +lo: Nat) -> Nat:
  Nat.add(65536n, Nat.add(Nat.mul(Nat.sub(hi, 55296n), 1024n), Nat.sub(lo, 56320n)))

# Walks the characters in order. pending is a high surrogate waiting for its low
# half. The state is threaded through a step that never recurses, so the walk
# itself is structural on the characters.
type Unpair is Data:
  Unpair{pending: Maybe<&2, Nat>, acc: List<&2, Char>}

def Unpair.emit(c: Char, acc: List<&2, Char>) -> Maybe<&2, Unpair>:
  Some{Unpair{None{}, c <> acc}}

def Unpair.pick(p: Maybe<&2, Nat>, hi: Bool, lo: Bool, +n: Nat, c: Char, acc: List<&2, Char>) -> Maybe<&2, Unpair>:
  match p hi lo:
    case None{} True{} _:
      Some{Unpair{Some{n}, acc}}
    case None{} False{} True{}:
      None{}
    case None{} False{} False{}:
      Unpair.emit(c, acc)
    case Some{h} _ True{}:
      Unpair.emit(Text.char(Lex.pair(h, n)), acc)
    case Some{h} _ False{}:
      None{}

def Unpair.step(st: Maybe<&2, Unpair>, +c: Char) -> Maybe<&2, Unpair>:
  match st:
    case None{}:
      None{}
    case Some{Unpair{p, acc}}:
      Unpair.pick(p, Lex.high(Text.code(c)), Lex.low(Text.code(c)), Text.code(c), c, acc)

def Unpair.finish(st: Maybe<&2, Unpair>) -> Maybe<&2, String>:
  match st:
    case Some{Unpair{None{}, acc}}:
      Some{String.from_list(List.reverse(&2, Char, acc))}
    case other:
      None{}

def Lex.unpair(cs: List<&2, Char>, st: Maybe<&2, Unpair>) -> Maybe<&2, String>:
  match cs:
    case Nil{}:
      Unpair.finish(st)
    case Con{c, t}:
      Lex.unpair(t, Unpair.step(st, c))

def Lex.str.done(s: Maybe<&2, String>, out: List<&2, Tok>) -> Maybe<&2, Lexed>:
  match s:
    case None{}:
      None{}
    case Some{v}:
      Lex.go(LTop{}, TStr{v} <> out)

def Lex.str.end(cs: List<&2, Char>, out: List<&2, Tok>) -> Maybe<&2, Lexed>:
  Lex.str.done(Lex.unpair(List.reverse(&2, Char, cs), Some{Unpair{None{}, []}}), out)

def Lex.str.which(quote: Bool, slash: Bool, control: Bool, c: Char, buf: List<&2, Char>, out: List<&2, Tok>) -> Maybe<&2, Lexed>:
  match quote slash control:
    case True{} _ _:
      Lex.str.end(buf, out)
    case False{} True{} _:
      Lex.go(LEsc{buf}, out)
    case False{} False{} True{}:
      None{}
    case False{} False{} False{}:
      Lex.go(LStr{c <> buf}, out)

def Lex.str.pick(+n: Nat, c: Char, buf: List<&2, Char>, out: List<&2, Tok>) -> Maybe<&2, Lexed>:
  Lex.str.which(Nat.is_eq(n, 34n), Nat.is_eq(n, 92n), Nat.is_lt(n, 32n), c, buf, out)

def Lex.esc.put(n: Nat, buf: List<&2, Char>, out: List<&2, Tok>) -> Maybe<&2, Lexed>:
  Lex.go(LStr{Text.char(n) <> buf}, out)

def Lex.esc(n: Nat, buf: List<&2, Char>, out: List<&2, Tok>) -> Maybe<&2, Lexed>:
  match n:
    case 34n:
      Lex.esc.put(34n, buf, out)
    case 92n:
      Lex.esc.put(92n, buf, out)
    case 47n:
      Lex.esc.put(47n, buf, out)
    case 98n:
      Lex.esc.put(8n, buf, out)
    case 102n:
      Lex.esc.put(12n, buf, out)
    case 110n:
      Lex.esc.put(10n, buf, out)
    case 114n:
      Lex.esc.put(13n, buf, out)
    case 116n:
      Lex.esc.put(9n, buf, out)
    case 117n:
      Lex.go(LHex{buf, 0n, 4n}, out)
    case other:
      None{}

def Lex.hexval.pick(digit: Bool, lower: Bool, upper: Bool, +n: Nat) -> Nat:
  match digit lower upper:
    case True{} _ _:
      Nat.sub(n, 48n)
    case False{} True{} _:
      Nat.sub(n, 87n)
    case False{} False{} True{}:
      Nat.sub(n, 55n)
    case False{} False{} False{}:
      16n

# The value of a hex digit, or 16 for anything else.
def Lex.hexval(+n: Nat) -> Nat:
  Lex.hexval.pick(Nat.is_le(48n, n) && Nat.is_le(n, 57n), Nat.is_le(97n, n) && Nat.is_le(n, 102n), Nat.is_le(65n, n) && Nat.is_le(n, 70n), n)

def Lex.hex.more(more: Nat, +v: Nat, buf: List<&2, Char>, out: List<&2, Tok>) -> Maybe<&2, Lexed>:
  match more:
    case 0n:
      Lex.go(LStr{Text.char(v) <> buf}, out)
    case 1n+m:
      Lex.go(LHex{buf, v, 1n+m}, out)

def Lex.hex.left(left: Nat, +v: Nat, buf: List<&2, Char>, out: List<&2, Tok>) -> Maybe<&2, Lexed>:
  match left:
    case 0n:
      None{}
    case 1n+more:
      Lex.hex.more(more, v, buf, out)

def Lex.hex.pick(ok: Bool, +v: Nat, buf: List<&2, Char>, left: Nat, out: List<&2, Tok>) -> Maybe<&2, Lexed>:
  match ok:
    case False{}:
      None{}
    case True{}:
      Lex.hex.left(left, v, buf, out)

def Lex.hex(+h: Nat, buf: List<&2, Char>, +value: Nat, left: Nat, out: List<&2, Tok>) -> Maybe<&2, Lexed>:
  Lex.hex.pick(Nat.is_lt(h, 16n), Nat.add(Nat.mul(value, 16n), h), buf, left, out)

def Lex.num.more(refuse: Bool, value: Nat, digits: Nat, out: List<&2, Tok>) -> Maybe<&2, Lexed>:
  match refuse:
    case True{}:
      None{}
    case False{}:
      Lex.go(LNum{value, digits}, out)

def Lex.num.stop(refuse: Bool, c: Char, out: List<&2, Tok>) -> Maybe<&2, Lexed>:
  match refuse:
    case True{}:
      None{}
    case False{}:
      Lex.top(c, out)

def Lex.num.pick(digit: Bool, +n: Nat, c: Char, +value: Nat, +digits: Nat, out: List<&2, Tok>) -> Maybe<&2, Lexed>:
  match digit:
    case True{}:
      Lex.num.more(Nat.is_eq(value, 0n) || Nat.is_le(Json.Digits(), digits), Nat.add(Nat.mul(value, 10n), Nat.sub(n, 48n)), Nat.add(digits, 1n), out)
    case False{}:
      Lex.num.stop(Nat.is_eq(n, 46n) || Nat.is_eq(n, 101n) || Nat.is_eq(n, 69n), c, TNum{value} <> out)

# A digit extends the number, up to Json.Digits() digits and with no leading
# zero. Anything else ends it and is lexed as a fresh character, except a
# fraction or exponent, which is refused.
def Lex.num(+n: Nat, c: Char, +value: Nat, +digits: Nat, out: List<&2, Tok>) -> Maybe<&2, Lexed>:
  Lex.num.pick(Nat.is_le(48n, n) && Nat.is_le(n, 57n), n, c, value, digits, out)

def Lex.word.pick(same: Bool, more: String, tok: Tok, out: List<&2, Tok>) -> Maybe<&2, Lexed>:
  match same more:
    case False{} _:
      None{}
    case True{} SNil{}:
      Lex.go(LTop{}, tok <> out)
    case True{} m:
      Lex.go(LWord{m, tok}, out)

def Lex.word(rest: String, tok: Tok, c: Char, out: List<&2, Tok>) -> Maybe<&2, Lexed>:
  match rest:
    case SNil{}:
      None{}
    case SCon{r, more}:
      Lex.word.pick(Nat.is_eq(Text.code(r), Text.code(c)), more, tok, out)

def Lex.step.mode(mode: Lex, +c: Char, out: List<&2, Tok>) -> Maybe<&2, Lexed>:
  match mode:
    case LTop{}:
      Lex.top(c, out)
    case LStr{buf}:
      Lex.str.pick(Text.code(c), c, buf, out)
    case LEsc{buf}:
      Lex.esc(Text.code(c), buf, out)
    case LHex{buf, value, left}:
      Lex.hex(Lex.hexval(Text.code(c)), buf, value, left, out)
    case LNum{value, digits}:
      Lex.num(Text.code(c), c, value, digits, out)
    case LWord{rest, tok}:
      Lex.word(rest, tok, c, out)

def Lex.step(st: Maybe<&2, Lexed>, c: Char) -> Maybe<&2, Lexed>:
  match st:
    case None{}:
      None{}
    case Some{Lexed{mode, out}}:
      Lex.step.mode(mode, c, out)

def Lex.finish(st: Maybe<&2, Lexed>) -> Maybe<&2, List<&2, Tok>>:
  match st:
    case None{}:
      None{}
    case Some{Lexed{LTop{}, out}}:
      Some{List.reverse(&2, Tok, out)}
    case Some{Lexed{LNum{value, digits}, out}}:
      Some{List.reverse(&2, Tok, TNum{value} <> out)}
    case Some{other}:
      None{}

def Lex.run(s: String, st: Maybe<&2, Lexed>) -> Maybe<&2, List<&2, Tok>>:
  match s:
    case SNil{}:
      Lex.finish(st)
    case SCon{c, t}:
      Lex.run(t, Lex.step(st, c))

def Json.lex(s: String) -> Maybe<&2, List<&2, Tok>>:
  Lex.run(s, Lex.go(LTop{}, []))

# Parsing
# -------

# An open array or object. An object's key waits in key until its value comes.
type Frame is Data:
  FArr{rev: List<&2, Json>}
  FObj{rev: List<&2, Member>, key: String}

# What the next token may be.
type Want is Data:
  WValue{}
  WFirst{}
  WKey{}
  WFirstKey{}
  WColon{}
  WAfter{}
  WEnd{}

type Parse is Data:
  Parse{want: Want, stack: List<&2, Frame>, done: Json}

def Parse.go(want: Want, stack: List<&2, Frame>) -> Maybe<&2, Parse>:
  Some{Parse{want, stack, JNull{}}}

# A finished value goes into the frame below it, or ends the document.
def Parse.value(v: Json, stack: List<&2, Frame>) -> Maybe<&2, Parse>:
  match stack:
    case Nil{}:
      Some{Parse{WEnd{}, [], v}}
    case Con{FArr{rev}, rest}:
      Parse.go(WAfter{}, FArr{v <> rev} <> rest)
    case Con{FObj{rev, k}, rest}:
      Parse.go(WAfter{}, FObj{Member{k, v} <> rev, ""} <> rest)

def Parse.close.arr(stack: List<&2, Frame>) -> Maybe<&2, Parse>:
  match stack:
    case Con{FArr{rev}, rest}:
      Parse.value(JArr{Json.items(rev, JNil{})}, rest)
    case other:
      None{}

def Parse.close.obj(stack: List<&2, Frame>) -> Maybe<&2, Parse>:
  match stack:
    case Con{FObj{rev, k}, rest}:
      Parse.value(JObj{Json.fields(rev, JNil{})}, rest)
    case other:
      None{}

def Parse.comma(stack: List<&2, Frame>) -> Maybe<&2, Parse>:
  match stack:
    case Con{FArr{rev}, rest}:
      Parse.go(WValue{}, FArr{rev} <> rest)
    case Con{FObj{rev, k}, rest}:
      Parse.go(WKey{}, FObj{rev, k} <> rest)
    case Nil{}:
      None{}

def Parse.key(k: String, stack: List<&2, Frame>) -> Maybe<&2, Parse>:
  match stack:
    case Con{FObj{rev, old}, rest}:
      Parse.go(WColon{}, FObj{rev, k} <> rest)
    case other:
      None{}

def Parse.start(t: Tok, stack: List<&2, Frame>) -> Maybe<&2, Parse>:
  match t:
    case TStr{s}:
      Parse.value(JStr{s}, stack)
    case TNum{n}:
      Parse.value(JNum{n}, stack)
    case TLit{v}:
      Parse.value(v, stack)
    case TLeft{}:
      Parse.go(WFirst{}, FArr{[]} <> stack)
    case TOpen{}:
      Parse.go(WFirstKey{}, FObj{[], ""} <> stack)
    case other:
      None{}

def Parse.first(t: Tok, stack: List<&2, Frame>) -> Maybe<&2, Parse>:
  match t:
    case TRight{}:
      Parse.close.arr(stack)
    case other:
      Parse.start(other, stack)

def Parse.firstkey(t: Tok, stack: List<&2, Frame>) -> Maybe<&2, Parse>:
  match t:
    case TClose{}:
      Parse.close.obj(stack)
    case TStr{k}:
      Parse.key(k, stack)
    case other:
      None{}

def Parse.wantkey(t: Tok, stack: List<&2, Frame>) -> Maybe<&2, Parse>:
  match t:
    case TStr{k}:
      Parse.key(k, stack)
    case other:
      None{}

def Parse.colon(t: Tok, stack: List<&2, Frame>) -> Maybe<&2, Parse>:
  match t:
    case TColon{}:
      Parse.go(WValue{}, stack)
    case other:
      None{}

def Parse.after(t: Tok, stack: List<&2, Frame>) -> Maybe<&2, Parse>:
  match t:
    case TComma{}:
      Parse.comma(stack)
    case TRight{}:
      Parse.close.arr(stack)
    case TClose{}:
      Parse.close.obj(stack)
    case other:
      None{}

def Parse.step(st: Maybe<&2, Parse>, t: Tok) -> Maybe<&2, Parse>:
  match st:
    case None{}:
      None{}
    case Some{Parse{WValue{}, stack, d}}:
      Parse.start(t, stack)
    case Some{Parse{WFirst{}, stack, d}}:
      Parse.first(t, stack)
    case Some{Parse{WKey{}, stack, d}}:
      Parse.wantkey(t, stack)
    case Some{Parse{WFirstKey{}, stack, d}}:
      Parse.firstkey(t, stack)
    case Some{Parse{WColon{}, stack, d}}:
      Parse.colon(t, stack)
    case Some{Parse{WAfter{}, stack, d}}:
      Parse.after(t, stack)
    case Some{Parse{WEnd{}, stack, d}}:
      None{}

def Parse.finish(st: Maybe<&2, Parse>) -> Maybe<&2, Json>:
  match st:
    case Some{Parse{WEnd{}, stack, d}}:
      Some{d}
    case other:
      None{}

def Parse.run(ts: List<&2, Tok>, st: Maybe<&2, Parse>) -> Maybe<&2, Json>:
  match ts:
    case Nil{}:
      Parse.finish(st)
    case Con{t, rest}:
      Parse.run(rest, Parse.step(st, t))

def Json.parse.tokens(ts: Maybe<&2, List<&2, Tok>>) -> Maybe<&2, Json>:
  match ts:
    case None{}:
      None{}
    case Some{xs}:
      Parse.run(xs, Parse.go(WValue{}, []))

# The document's one value, or None for anything that isn't JSON this parser
# reads: see Json for what it refuses.
def Json.parse(s: String) -> Maybe<&2, Json>:
  Json.parse.tokens(Json.lex(s))
