import Base

# SHA-256, as FIPS 180-4 defines it. Base has no crypto, and the web process
# keeps only the hash of each API key, so it hashes the key a request brings
# and looks for that. Pure, so the scenarios and scripts/sha256.test.mjs check
# it against known digests and Node's crypto.
#
# Bytes are U32s from 0 to 255, and a message is at most 2^29 bytes, so its bit
# length fits the low word of the length field. Keys are far shorter.

def Sha.k() -> List<&2, U32>:
  [1116352408, 1899447441, 3049323471, 3921009573, 961987163, 1508970993, 2453635748, 2870763221,
   3624381080, 310598401, 607225278, 1426881987, 1925078388, 2162078206, 2614888103, 3248222580,
   3835390401, 4022224774, 264347078, 604807628, 770255983, 1249150122, 1555081692, 1996064986,
   2554220882, 2821834349, 2952996808, 3210313671, 3336571891, 3584528711, 113926993, 338241895,
   666307205, 773529912, 1294757372, 1396182291, 1695183700, 1986661051, 2177026350, 2456956037,
   2730485921, 2820302411, 3259730800, 3345764771, 3516065817, 3600352804, 4094571909, 275423344,
   430227734, 506948616, 659060556, 883997877, 958139571, 1322822218, 1537002063, 1747873779,
   1955562222, 2024104815, 2227730452, 2361852424, 2428436474, 2756734187, 3204031479, 3329325298]

type Words is Data:
  Words{a: U32, b: U32, c: U32, d: U32, e: U32, f: U32, g: U32, h: U32}

def Sha.start() -> Words:
  Words{1779033703, 3144134277, 1013904242, 2773480762, 1359893119, 2600822924, 528734635, 1541459225}

def Sha.rotr(+x: U32, +n: Nat) -> U32:
  U32.or(U32.shrn(x, n), U32.shln(x, Nat.sub(32n, n)))

def Sha.big0(+x: U32) -> U32:
  U32.xor(U32.xor(Sha.rotr(x, 2n), Sha.rotr(x, 13n)), Sha.rotr(x, 22n))

def Sha.big1(+x: U32) -> U32:
  U32.xor(U32.xor(Sha.rotr(x, 6n), Sha.rotr(x, 11n)), Sha.rotr(x, 25n))

def Sha.small0(+x: U32) -> U32:
  U32.xor(U32.xor(Sha.rotr(x, 7n), Sha.rotr(x, 18n)), U32.shrn(x, 3n))

def Sha.small1(+x: U32) -> U32:
  U32.xor(U32.xor(Sha.rotr(x, 17n), Sha.rotr(x, 19n)), U32.shrn(x, 10n))

def Sha.ch(+e: U32, f: U32, g: U32) -> U32:
  U32.xor(U32.and(e, f), U32.and(U32.not(e), g))

def Sha.maj(+a: U32, +b: U32, +c: U32) -> U32:
  U32.xor(U32.xor(U32.and(a, b), U32.and(a, c)), U32.and(b, c))

def Sha.at(+ws: List<&2, U32>, n: Nat) -> U32:
  Maybe.default(&2, U32, List.get(&2, U32, ws, n), 0)

# The message schedule, newest word first: each new word comes from the words
# 2, 7, 15 and 16 places back.
def Sha.schedule(fuel: Nat, +ws: List<&2, U32>) -> List<&2, U32>:
  match fuel:
    case 0n:
      ws
    case 1n+f:
      Sha.schedule(f, (Sha.small1(Sha.at(ws, 1n)) + Sha.at(ws, 6n) + Sha.small0(Sha.at(ws, 14n)) + Sha.at(ws, 15n) : U32) <> ws)

def Sha.round(+k: U32, +w: U32, s: Words) -> Words:
  match s:
    case Words{+a, +b, +c, d, +e, +f, +g, h}:
      +t1 = (h + Sha.big1(e) + Sha.ch(e, f, g) + k + w : U32)
      +t2 = (Sha.big0(a) + Sha.maj(a, b, c) : U32)
      Words{(t1 + t2 : U32), a, b, c, (d + t1 : U32), e, f, g}

def Sha.rounds(ks: List<&2, U32>, ws: List<&2, U32>, s: Words) -> Words:
  match ks ws:
    case Con{k, kt} Con{w, wt}:
      Sha.rounds(kt, wt, Sha.round(k, w, s))
    case _ _:
      s

def Sha.add(x: Words, y: Words) -> Words:
  match x y:
    case Words{a, b, c, d, e, f, g, h} Words{a2, b2, c2, d2, e2, f2, g2, h2}:
      Words{(a + a2 : U32), (b + b2 : U32), (c + c2 : U32), (d + d2 : U32), (e + e2 : U32), (f + f2 : U32), (g + g2 : U32), (h + h2 : U32)}

# One 16-word block into the running hash.
def Sha.block(block: List<&2, U32>, +s: Words) -> Words:
  Sha.add(s, Sha.rounds(Sha.k(), List.reverse(&2, U32, Sha.schedule(48n, List.reverse(&2, U32, block))), s))

def Sha.blocks(fuel: Nat, +ws: List<&2, U32>, +s: Words) -> Words:
  match fuel:
    case 0n:
      s
    case 1n+f:
      Sha.blocks(f, List.drop(&2, U32, ws, 16n), Sha.block(List.take(&2, U32, ws, 16n), s))

# Big-endian words from bytes, four at a time. The padding makes the count a
# multiple of four.
def Sha.words(bs: List<&2, U32>) -> List<&2, U32>:
  match bs:
    case Con{a, Con{b, Con{c, Con{d, rest}}}}:
      U32.or(U32.or(U32.shln(a, 24n), U32.shln(b, 16n)), U32.or(U32.shln(c, 8n), d)) <> Sha.words(rest)
    case other:
      []

# The zero bytes that bring n bytes, plus the 0x80 and the 8 length bytes, to a
# multiple of 64.
def Sha.zeros(+n: Nat) -> Nat:
  Nat.mod(Nat.sub(Nat.add(64n, 55n), Nat.mod(n, 64n)), 64n)

def Sha.byte(+bits: Nat, shift: Nat) -> U32:
  U32.from_nat(Nat.mod(Nat.div(bits, Nat.pow(2n, shift)), 256n))

# The 8-byte big-endian bit length. The top four bytes are zero for any
# message under 2^29 bytes.
def Sha.length(+n: Nat) -> List<&2, U32>:
  +bits = Nat.mul(n, 8n)
  [0, 0, 0, 0, Sha.byte(bits, 24n), Sha.byte(bits, 16n), Sha.byte(bits, 8n), Sha.byte(bits, 0n)]

def Sha.pad(+bs: List<&2, U32>) -> List<&2, U32>:
  +n = List.length(&2, U32, bs)
  List.append(&2, U32, bs, List.append(&2, U32, 128 <> List.replicate(U32, Sha.zeros(n), 0), Sha.length(n)))

def Sha.nibble.pick(digit: Bool, n: Nat) -> Char:
  match digit:
    case True{}:
      Chr{U32.from_nat(Nat.add(48n, n))}
    case False{}:
      Chr{U32.from_nat(Nat.add(87n, n))}

def Sha.nibble(+n: Nat) -> Char:
  Sha.nibble.pick(Nat.is_lt(n, 10n), n)

def Sha.hex.word(fuel: Nat, +w: Nat, acc: String) -> String:
  match fuel:
    case 0n:
      acc
    case 1n+f:
      Sha.hex.word(f, Nat.div(w, 16n), SCon{Sha.nibble(Nat.mod(w, 16n)), acc})

def Sha.hex(s: Words) -> String:
  match s:
    case Words{a, b, c, d, e, f, g, h}:
      Sha.hex.word(8n, U32.to_nat(a), "") ++ Sha.hex.word(8n, U32.to_nat(b), "") ++ Sha.hex.word(8n, U32.to_nat(c), "") ++ Sha.hex.word(8n, U32.to_nat(d), "")
        ++ Sha.hex.word(8n, U32.to_nat(e), "") ++ Sha.hex.word(8n, U32.to_nat(f), "") ++ Sha.hex.word(8n, U32.to_nat(g), "") ++ Sha.hex.word(8n, U32.to_nat(h), "")

# The digest of the bytes, as 64 lowercase hex digits.
def Sha.bytes(+bs: List<&2, U32>) -> String:
  +ws = Sha.words(Sha.pad(bs))
  Sha.hex(Sha.blocks(Nat.div(List.length(&2, U32, ws), 16n), ws, Sha.start()))

def Sha.ascii(s: String) -> List<&2, U32>:
  match s:
    case SNil{}:
      []
    case SCon{c, t}:
      Char.to_u32(c) <> Sha.ascii(t)

# The digest of a string of characters below 128, each one byte. API keys and
# the admin key are ASCII, and the shell refuses a token that isn't.
def Sha.text(s: String) -> String:
  Sha.bytes(Sha.ascii(s))
