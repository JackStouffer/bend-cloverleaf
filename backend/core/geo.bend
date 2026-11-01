import Base
import ./types.bend as T

# Straight-line drive times, standing in until the road network exists. No proof
# looks inside minutes, so swapping in real road times changes no proof.

def gap(+a: Nat, +b: Nat) -> Nat:
  Nat.add(Nat.sub(a, b), Nat.sub(b, a))

# Bhaskara's approximation of 1000 * cos(degrees), within 0.2% across the lower 48.
def cos_milli(+deg: Nat) -> Nat:
  +sq = Nat.mul(deg, deg)
  Nat.div(Nat.mul(1000n, Nat.sub(32400n, Nat.mul(4n, sq))), Nat.add(32400n, sq))


def isqrt.if(stop: Bool, x: Nat, next: Unit -> Nat) -> Nat:
  match stop:
    case True{}:
      x
    case False{}:
      next(Unit{})

# Newton's method from above. fuel only guards termination: the start is within
# 13% of the root, so a few steps are always enough.
def isqrt.go(fuel: Nat, +n: Nat, +x: Nat) -> Nat:
  match fuel:
    case 0n:
      x
    case 1n+f:
      +y = Nat.div(Nat.add(x, Nat.div(n, x)), 2n)
      isqrt.if(Nat.is_ge(y, x), x, u => isqrt.go(f, n, y))

# sqrt(a^2 + b^2), starting from an estimate that's never below the root.
def hypot(+a: Nat, +b: Nat) -> Nat:
  +hi = Nat.max(a, b)
  +lo = Nat.min(a, b)
  +n = Nat.add(Nat.mul(a, a), Nat.mul(b, b))
  isqrt.go(8n, n, Nat.add(1n, Nat.add(hi, Nat.div(lo, 2n))))

# Tenths of a mile between two points, about 69 miles to a degree.
def tenths(+a: T.Point, +b: T.Point) -> Nat:
  +dlat = gap(T.Point.lat(a), T.Point.lat(b))
  +dlon = gap(T.Point.lon(a), T.Point.lon(b))
  +mid = Nat.div(Nat.add(T.Point.lat(a), T.Point.lat(b)), 20000n)
  +north = Nat.div(Nat.mul(dlat, 69n), 1000n)
  +east = Nat.div(Nat.mul(Nat.div(Nat.mul(dlon, 69n), 1000n), cos_milli(mid)), 1000n)
  hypot(north, east)

# Drive minutes, rounded up: roads run 1.3 times the straight line at 45 mph.
def minutes(+a: T.Point, +b: T.Point) -> Nat:
  Nat.div(Nat.add(Nat.mul(tenths(a, b), 13n), 74n), 75n)
