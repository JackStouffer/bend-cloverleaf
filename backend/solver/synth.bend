import Base
import ../core/types.bend as T

# Synthetic instances for the benchmark: a small fixed-seed generator, so runs
# compare like with like. The real generator comes with the national solver.

def next(+x: Nat) -> Nat:
  Nat.mod(Nat.add(Nat.mul(x, 48271n), 11n), 2147483647n)

# Metro areas as (lat, degrees west), times 10000.
def Metros.size() -> Nat:
  8n

def Metros.lat(i: Nat) -> Nat:
  match i:
    case 0n:
      406000n
    case 1n:
      340000n
    case 2n:
      418000n
    case 3n:
      297000n
    case 4n:
      334000n
    case 5n:
      337000n
    case 6n:
      397000n
    case 1n+1n+1n+1n+1n+1n+1n+p:
      476000n

def Metros.lon(i: Nat) -> Nat:
  match i:
    case 0n:
      740000n
    case 1n:
      1182000n
    case 2n:
      876000n
    case 3n:
      953000n
    case 4n:
      1120000n
    case 5n:
      843000n
    case 6n:
      1049000n
    case 1n+1n+1n+1n+1n+1n+1n+p:
      1223000n

# A metro's zips are its index times 100, plus an area from 0 to 19, so
# neighbouring contractors overlap.
def Point.near(+m: Nat, +x: Nat) -> T.Point:
  +a = Nat.mod(x, 6000n)
  +b = Nat.mod(Nat.div(x, 6000n), 6000n)
  T.Point{Nat.sub(Nat.add(Metros.lat(m), a), 3000n), Nat.sub(Nat.add(Metros.lon(m), b), 3000n)}

def area(+p: T.Point, +m: Nat) -> Nat:
  +a = Nat.div(Nat.sub(Nat.add(T.Point.lat(p), 3000n), Metros.lat(m)), 1500n)
  +b = Nat.div(Nat.sub(Nat.add(T.Point.lon(p), 3000n), Metros.lon(m)), 1500n)
  Nat.add(Nat.mul(m, 100n), Nat.add(Nat.mul(a, 4n), b))

def zips.go(+n: Nat, +base: Nat, acc: List<&2, Nat>) -> List<&2, Nat>:
  match n:
    case 0n:
      acc
    case 1n+p:
      zips.go(p, base, Nat.add(base, p) <> acc)

def days.go(+n: Nat, +first: Nat, acc: List<&2, Nat>) -> List<&2, Nat>:
  match n:
    case 0n:
      acc
    case 1n+p:
      days.go(p, first, Nat.add(first, p) <> acc)

def crews(n: Nat, +id: Nat, +x: Nat, +first: Nat, +span: Nat) -> List<&2, T.Contractor>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      +y = next(next(x))
      +m = Nat.mod(id, Metros.size())
      +z = Nat.add(Nat.mul(m, 100n), Nat.mod(y, 8n))
      T.Contractor{id, Point.near(m, y), zips.go(8n, z, Nil{}), 480n, days.go(span, first, Nil{}), 0n} <> crews(p, 1n+id, y, first, span)

def jobs(n: Nat, +id: Nat, +x: Nat, +first: Nat, +span: Nat) -> List<&2, T.Appraisal>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      +y = next(next(x))
      +m = Nat.mod(id, Metros.size())
      +site = Point.near(m, y)
      T.Appraisal{id, site, area(site, m), Nat.add(first, Nat.mod(next(y), span)), 20n, 0n} <> jobs(p, 1n+id, y, first, span)

def instance(+crew_count: Nat, +job_count: Nat, +first: Nat, +span: Nat) -> T.Instance:
  T.Instance{crews(crew_count, 1n, 7n, first, span), jobs(job_count, 1n, 12345n, first, span), 60n, 0n}
