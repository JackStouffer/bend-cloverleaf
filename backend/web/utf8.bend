import Base

import ./json.bend as J

# UTF-8 bytes to a String. The shell reads sockets and files as bytes, because
# a String read can cut a character in two at the end of a chunk, and Base has
# no decoder. A byte that doesn't start a well-formed character becomes U+FFFD
# on its own, and decoding goes on from the next byte.

type Glyph is Data:
  Glyph{code: Nat, width: Nat}

def Glyph.code(g: Glyph) -> Nat:
  match g:
    case Glyph{c, w}:
      c

def Glyph.width(g: Glyph) -> Nat:
  match g:
    case Glyph{c, w}:
      w

def Utf8.bad() -> Glyph:
  Glyph{65533n, 1n}

def Utf8.in(+n: Nat, lo: Nat, hi: Nat) -> Bool:
  Nat.is_le(lo, n) && Nat.is_le(n, hi)

def Utf8.cont(+n: Nat) -> Bool:
  Utf8.in(n, 128n, 191n)

def Utf8.nat(m: Maybe<&2, U32>) -> Nat:
  match m:
    case None{}:
      256n
    case Some{x}:
      U32.to_nat(x)

# The byte i places into rest, or 256 past its end.
def Utf8.byte(+rest: List<&2, U32>, i: Nat) -> Nat:
  Utf8.nat(List.get(&2, U32, rest, i))

def Utf8.keep(ok: Bool, code: Nat, width: Nat) -> Glyph:
  match ok:
    case True{}:
      Glyph{code, width}
    case False{}:
      Utf8.bad()

def Utf8.two(b: Nat, +c1: Nat) -> Glyph:
  Utf8.keep(Utf8.cont(c1), Nat.add(Nat.mul(Nat.sub(b, 192n), 64n), Nat.sub(c1, 128n)), 2n)

def Utf8.three(b: Nat, +c1: Nat, +c2: Nat) -> Glyph:
  Utf8.keep(Utf8.cont(c1) && Utf8.cont(c2),
    Nat.add(Nat.add(Nat.mul(Nat.sub(b, 224n), 4096n), Nat.mul(Nat.sub(c1, 128n), 64n)), Nat.sub(c2, 128n)), 3n)

def Utf8.four(b: Nat, +c1: Nat, +c2: Nat, +c3: Nat) -> Glyph:
  Utf8.keep(Utf8.cont(c1) && Utf8.cont(c2) && Utf8.cont(c3),
    Nat.add(Nat.add(Nat.add(Nat.mul(Nat.sub(b, 240n), 262144n), Nat.mul(Nat.sub(c1, 128n), 4096n)), Nat.mul(Nat.sub(c2, 128n), 64n)), Nat.sub(c3, 128n)), 4n)

def Utf8.pick(hit: Bool, g: Glyph, rest: Glyph) -> Glyph:
  match hit:
    case True{}:
      g
    case False{}:
      rest

# The character that starts with byte b, with the bytes after it in rest.
def Utf8.glyph(+b: Nat, +rest: List<&2, U32>) -> Glyph:
  Utf8.pick(Nat.is_lt(b, 128n), Glyph{b, 1n},
    Utf8.pick(Utf8.in(b, 194n, 223n), Utf8.two(b, Utf8.byte(rest, 0n)),
      Utf8.pick(Utf8.in(b, 224n, 239n), Utf8.three(b, Utf8.byte(rest, 0n), Utf8.byte(rest, 1n)),
        Utf8.pick(Utf8.in(b, 240n, 244n), Utf8.four(b, Utf8.byte(rest, 0n), Utf8.byte(rest, 1n), Utf8.byte(rest, 2n)),
          Utf8.bad()))))

# The fuel is the number of bytes, so each step costs one. The text so far is
# reversed in acc.
def Utf8.go(fuel: Nat, bs: List<&2, U32>, acc: String) -> String:
  match fuel bs:
    case 0n _:
      String.reverse(acc)
    case 1n+f Nil{}:
      String.reverse(acc)
    case 1n+f Con{b, +rest}:
      +g = Utf8.glyph(U32.to_nat(b), rest)
      Utf8.go(f, List.drop(&2, U32, rest, Nat.sub(Glyph.width(g), 1n)), SCon{J.Text.char(Glyph.code(g)), acc})

def Utf8.decode(+bs: List<&2, U32>) -> String:
  Utf8.go(List.length(&2, U32, bs), bs, "")
