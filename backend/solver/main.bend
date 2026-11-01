import Base
import ../core/types.bend as T
import ../core/plan.bend as P
import ../core/solve.bend as S
import ./synth.bend as Syn

# Runs the planner on a synthetic instance and reports how it did. Usage:
#   solver <crews> <jobs> <days>

def stops(routes: List<&2, T.Route>) -> Nat:
  match routes:
    case Nil{}:
      0n
    case +r <> t:
      Nat.add(List.length(&2, T.Stop, T.Route.stops(r)), stops(t))

def used(routes: List<&2, T.Route>) -> Nat:
  match routes:
    case Nil{}:
      0n
    case +r <> t:
      Nat.add(U32.to_nat(Bool.to_u32(Bool.not(List.is_empty(&2, T.Stop, T.Route.stops(r))))), used(t))

def outside(routes: List<&2, T.Route>) -> Nat:
  match routes:
    case Nil{}:
      0n
    case +r <> t:
      Nat.add(List.length(&2, Nat, T.Audit.outside(T.Route.audit(r))), outside(t))

def report(+name: String, +plan: T.Plan) -> IO(Unit):
  +routes = T.Plan.routes(plan)
  IO.print(name ++ ": stops " ++ Nat.show(stops(routes))
    ++ ", routes used " ++ Nat.show(used(routes)) ++ ", outside " ++ Nat.show(outside(routes))
    ++ ", backlog " ++ Nat.show(List.length(&2, T.Appraisal, T.Plan.backlog(plan)))
    ++ ", exceptions " ++ Nat.show(List.length(&2, T.Exception, T.Plan.exceptions(plan)))
    ++ ", score " ++ Nat.show(S.score(plan)))

def verdict(c: Bool) -> String:
  match c:
    case True{}:
      "valid"
    case False{}:
      "INVALID"

def run(+crew_count: Nat, +job_count: Nat, +days: Nat) -> IO(Unit):
  do IO<Unit>:
    +inst : T.Instance = Syn.instance(crew_count, job_count, 20000n, days)
    IO.print("jobs " ++ Nat.show(List.length(&2, T.Appraisal, T.Instance.jobs(inst))))
    +t1 : Nat <- IO.now()
    +first : T.Plan = S.plan(S.Tuning.standard(), inst, 20000n, Nat.add(20000n, days))
    report("assign", first)
    +t2 : Nat <- IO.now()
    IO.print("assign took " ++ Nat.show(Nat.sub(t2, t1)) ++ "ms")
    +best : T.Plan = S.improve(3n, inst, first)
    report("improve", best)
    +t3 : Nat <- IO.now()
    IO.print("improve took " ++ Nat.show(Nat.sub(t3, t2)) ++ "ms")
    +out : T.Plan = S.publish(inst, best)
    IO.print("published: " ++ verdict(P.Plan.valid(inst, out)))
    +t4 : Nat <- IO.now()
    IO.print("publish took " ++ Nat.show(Nat.sub(t4, t3)) ++ "ms")

def num(s: String, d: Nat) -> Nat:
  Maybe.default(&2, Nat, Nat.read(s), d)

def start(args: List<String>) -> IO(Unit):
  match args:
    case p <> a <> b <> c <> r:
      run(num(a, 100n), num(b, 1000n), num(c, 7n))
    case _:
      run(100n, 1000n, 7n)

def main() -> IO(Unit):
  IO.bind(List<String>, Unit, IO.args(), start)
