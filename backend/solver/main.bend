import Base
import ../core/types.bend as T
import ../core/times.bend as Tm
import ../core/plan.bend as P
import ../core/solve.bend as S
import ../core/nation.bend as N
import ../road/main.bend as RM
import ./synth.bend as Syn
import ./load.bend as Ld
import ./report.bend as Rp
import ./baseline.bend as B

# The solver process's IO shell. Usage:
#   solver national <synth folder> <planner> <limit> <forks> <state>...
#   solver times <synth folder> <state> <limit>
#   solver <crews> <jobs> <days>
#
# national loads each state's instance.bin and matrix.bin from its folder,
# solves every state with `planner` (planner, first_fit or nearest), checks each
# plan with the proven checker, writes it to plan-<planner>.bin beside its
# inputs, and prints a report. `limit` is the matrix's search limit in
# deciseconds and `forks` how many times the states split in two. times writes
# one state's times.bin: the point count, then the minutes between every pair
# of points, as the solver sees them, for an outside solver to compare against.
# The last form is the straight-line benchmark on a small synthetic instance.

# Files bigger than this are refused before anything is read. A state's matrix
# for 4,000 points is 64MB.
def Max.bytes() -> Nat:
  64000004n

def Chunk() -> U32:
  786432

# Reading
# -------

def Words.file(+path: String) -> IO(List<&2, Nat>):
  do IO<List<&2, Nat>>:
    +bytes : Nat <- RM.Size.file(path)
    RM.Need(Nat.is_le(bytes, Max.bytes()), path ++ " is too big")
    xs : List<&2, Nat> <- RM.Fold.file(~List<&2, Nat>, ~Ld.Words.bytes, path, bytes, Chunk(), Nil{})
    return List.reverse(&2, Nat, xs)

def Mx.file(+path: String, +keys: List<&2, Nat>) -> IO(Ld.Mx):
  +n = List.length(&2, Nat, keys)
  +want = Nat.mul(4n, Nat.add(1n, Nat.mul(n, n)))
  do IO<Ld.Mx>:
    +bytes : Nat <- RM.Size.file(path)
    RM.Need(Bool.and(Nat.is_eq(bytes, want), Nat.is_le(bytes, Max.bytes())), path ++ " has " ++ Nat.show(bytes) ++ " bytes, and " ++ Nat.show(n) ++ " points need " ++ Nat.show(want))
    m : Ld.Mx <- RM.Fold.file(~Ld.Mx, ~Ld.Mx.bytes, path, bytes, Chunk(), Ld.Mx.start(keys))
    return m

def State.load(+dir: String, +name: String, +limit: Nat) -> IO(Ld.Got):
  +path = dir ++ "/" ++ name
  do IO<Ld.Got>:
    +words : List<&2, Nat> <- Words.file(path ++ "/instance.bin")
    +got : Ld.Got = Ld.instance(words)
    +inst : T.Instance = Ld.Got.inst(got)
    RM.Need(P.Instance.ok(inst), name ++ ": the instance is empty or not one state sorted by id")
    +keys : List<&2, Nat> = Ld.keys(inst)
    +m : Ld.Mx <- Mx.file(path ++ "/matrix.bin", keys)
    RM.Need(Ld.Mx.ok(m, List.length(&2, Nat, keys)), name ++ ": the matrix doesn't match the instance")
    return Ld.Got{Ld.with(inst, Ld.Mx.times(m, limit)), Ld.Got.first(got), Ld.Got.days(got)}

def States.load(names: List<&2, String>, +dir: String, +limit: Nat) -> IO(List<&2, Ld.Got>):
  match names:
    case Nil{}:
      IO.pure(List<&2, Ld.Got>, Nil{})
    case +n <> t:
      do IO<List<&2, Ld.Got>>:
        g : Ld.Got <- State.load(dir, n, limit)
        rest : List<&2, Ld.Got> <- States.load(t, dir, limit)
        return g <> rest

def Gots.insts(gs: List<&2, Ld.Got>) -> List<&2, T.Instance>:
  match gs:
    case Nil{}:
      Nil{}
    case g <> t:
      Ld.Got.inst(g) <> Gots.insts(t)

def Gots.first(gs: List<&2, Ld.Got>) -> Nat:
  match gs:
    case Nil{}:
      0n
    case g <> t:
      Ld.Got.first(g)

def Gots.days(gs: List<&2, Ld.Got>) -> Nat:
  match gs:
    case Nil{}:
      0n
    case g <> t:
      Ld.Got.days(g)

# Writing
# -------

def Written(p: File & Result<&1, &1, U32 & String, Unit>) -> IO(File):
  (f, r) = p
  match r:
    case Done{_}:
      IO.pure(File, f)
    case Fail{_}:
      IO.die(File, 1, "could not write a file")

def U32s(xs: List<&2, Nat>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> t:
      U32.from_nat(x) <> U32s(t)

def Words.save(+path: String, +words: List<&2, Nat>) -> IO(Unit):
  do IO<Unit>:
    f : File <- IO.try(File, File.open(path, "w"))
    p : File & Result<&1, &1, U32 & String, Unit> <- File.write_bytes(f, RM.Bytes.row(U32s(words), Nil{}))
    f2 : File <- Written(p)
    File.close(f2)

# Solving
# -------

def Base.one(near: Bool, +i: T.Instance, +first: Nat, +last: Nat) -> T.Plan:
  match near:
    case True{}:
      B.nearest(i, first, last)
    case False{}:
      B.first_fit(i, first, last)

def Base.each(xs: List<&2, T.Instance>, +near: Bool, +first: Nat, +last: Nat) -> List<&2, T.Plan>:
  match xs:
    case Nil{}:
      Nil{}
    case +i <> t:
      Base.one(near, i, first, last) <> Base.each(t, near, first, last)

def Solve.all(+mode: Nat, +forks: Nat, +xs: List<&2, T.Instance>, +first: Nat, +last: Nat) -> List<&2, T.Plan>:
  match mode:
    case 0n:
      N.national(forks, S.Tuning.standard(), xs, first, last)
    case 1n:
      Base.each(xs, False{}, first, last)
    case 1n+1n+p:
      Base.each(xs, True{}, first, last)

def Mode.of(+name: String) -> Nat:
  Bool.pick(Nat, String.eq(name, "planner"), 0n, Bool.pick(Nat, String.eq(name, "first_fit"), 1n, Bool.pick(Nat, String.eq(name, "nearest"), 2n, 3n)))

# Reporting
# ---------

def isqrt(fuel: Nat, +n: Nat, +x: Nat) -> Nat:
  match fuel:
    case 0n:
      x
    case 1n+f:
      +y = Nat.div(Nat.add(x, Nat.div(n, x)), 2n)
      Bool.pick(Nat, Nat.is_ge(y, x), x, isqrt(f, n, y))

def Stats.line(s: Rp.Stats) -> String:
  match s:
    case Rp.Stats{r, +u, p, b, e, l, o, d, +w, k, +q, f, i, +c, +x, cm}:
      +n = Nat.max(u, 1n)
      +cn = Nat.max(c, 1n)
      +week = Nat.div(w, cn)
      +wvar = Nat.sub(Nat.div(x, cn), Nat.mul(week, week))
      +mean = Nat.div(w, n)
      +var = Nat.sub(Nat.div(q, n), Nat.mul(mean, mean))
      "placed " ++ Nat.show(p) ++ ", backlog " ++ Nat.show(b) ++ ", exceptions " ++ Nat.show(e)
        ++ " (" ++ Nat.show(i) ++ " don't fit an empty route), missed but feasible " ++ Nat.show(f) ++ ", late " ++ Nat.show(l) ++ ", outside " ++ Nat.show(o)
        ++ ", routes used " ++ Nat.show(u) ++ " of " ++ Nat.show(r) ++ ", drive " ++ Nat.show(d)
        ++ "m, day mean " ++ Nat.show(mean) ++ "m, sd " ++ Nat.show(isqrt(48n, var, Nat.add(var, 1n))) ++ "m, peak " ++ Nat.show(k) ++ "m, week per contractor " ++ Nat.show(week) ++ "m, sd " ++ Nat.show(isqrt(48n, wvar, Nat.add(wvar, 1n))) ++ "m, peak " ++ Nat.show(cm) ++ "m"

def Report.each(names: List<&2, String>, xs: List<&2, T.Instance>, ps: List<&2, T.Plan>, +dir: String, +mode: String, +first: Nat, +last: Nat, total: Rp.Stats) -> IO(Rp.Stats):
  match names xs ps:
    case +n <> nt +i <> it +p <> pt:
      do IO<Rp.Stats>:
        +s : Rp.Stats = Rp.of(i, p, first, last)
        RM.Need(P.Plan.check(i, p), n ++ ": the plan failed the checker")
        IO.print(n ++ ": crews " ++ Nat.show(List.length(&2, T.Contractor, T.Instance.crews(i))) ++ ", jobs " ++ Nat.show(List.length(&2, T.Appraisal, T.Instance.jobs(i))) ++ ", " ++ Stats.line(s))
        Words.save(dir ++ "/" ++ n ++ "/plan-" ++ mode ++ ".bin", Rp.Plan.words(p))
        out : Rp.Stats <- Report.each(nt, it, pt, dir, mode, first, last, Rp.Stats.add(total, s))
        return out
    case _ _ _:
      IO.pure(Rp.Stats, total)

def national(+dir: String, +mode: String, +limit: Nat, +forks: Nat, +names: List<&2, String>) -> IO(Unit):
  do IO<Unit>:
    RM.Need(Nat.is_lt(Mode.of(mode), 3n), "the planner is planner, first_fit or nearest, not " ++ mode)
    RM.Need(Nat.is_le(forks, 7n), "forks is at most 7")
    +t0 : Nat <- IO.now()
    +gots : List<&2, Ld.Got> <- States.load(names, dir, limit)
    +xs : List<&2, T.Instance> = Gots.insts(gots)
    +first : Nat = Gots.first(gots)
    +last : Nat = Nat.add(first, Gots.days(gots))
    +t1 : Nat <- IO.now()
    IO.print("loaded " ++ Nat.show(List.length(&2, T.Instance, xs)) ++ " states in " ++ Nat.show(Nat.sub(t1, t0)) ++ "ms")
    +plans : List<&2, T.Plan> = Solve.all(Mode.of(mode), forks, xs, first, last)
    +t2 : Nat <- IO.now()
    IO.print("solved with " ++ mode ++ " in " ++ Nat.show(Nat.sub(t2, t1)) ++ "ms")
    +total : Rp.Stats <- Report.each(names, xs, plans, dir, mode, first, last, Rp.Stats.zero())
    IO.print("national: " ++ Stats.line(total))
    +t3 : Nat <- IO.now()
    IO.print("checked and reported in " ++ Nat.show(Nat.sub(t3, t2)) ++ "ms")

# Dense times
# -----------

def Dense.row(bs: List<&2, T.Point>, +t: T.Times, +a: T.Point, rest: List<&2, Nat>) -> List<&2, Nat>:
  match bs:
    case Nil{}:
      rest
    case +b <> u:
      Tm.minutes(t, a, b) <> Dense.row(u, t, a, rest)

def Dense.all(xs: List<&2, T.Point>, +t: T.Times, +bs: List<&2, T.Point>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case +a <> u:
      Dense.row(bs, t, a, Dense.all(u, t, bs))

def times(+dir: String, +name: String, +limit: Nat) -> IO(Unit):
  do IO<Unit>:
    g : Ld.Got <- State.load(dir, name, limit)
    +inst : T.Instance = Ld.Got.inst(g)
    +pts : List<&2, T.Point> = Ld.points(inst)
    Words.save(dir ++ "/" ++ name ++ "/times.bin", List.length(&2, T.Point, pts) <> Dense.all(pts, T.Instance.times(inst), pts))
    IO.print(name ++ ": wrote times for " ++ Nat.show(List.length(&2, T.Point, pts)) ++ " points")

# The straight-line benchmark
# ---------------------------

def stops(routes: List<&2, T.Route>) -> Nat:
  match routes:
    case Nil{}:
      0n
    case +r <> t:
      Nat.add(List.length(&2, T.Stop, T.Route.stops(r)), stops(t))

def report(+name: String, +plan: T.Plan) -> IO(Unit):
  IO.print(name ++ ": stops " ++ Nat.show(stops(T.Plan.routes(plan)))
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

# Commands
# --------

def usage() -> IO(Unit):
  IO.print("usage: solver national <synth folder> <planner> <limit> <forks> <state>...\n       solver times <synth folder> <state> <limit>\n       solver <crews> <jobs> <days>")

# Arguments arrive as an affine list, and the state names are needed twice.
def Names.copy(xs: List<String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case +h <> t:
      h <> Names.copy(t)

def Command.national(+dir: String, rest: List<String>) -> IO(Unit):
  match rest:
    case +mode <> +limit <> +forks <> names:
      do IO<Unit>:
        +l : Nat <- RM.Arg(limit)
        +f : Nat <- RM.Arg(forks)
        national(dir, mode, l, f, Names.copy(names))
    case _:
      usage()

def Command.times(+dir: String, rest: List<String>) -> IO(Unit):
  match rest:
    case +name <> +limit <> _:
      do IO<Unit>:
        +l : Nat <- RM.Arg(limit)
        times(dir, name, l)
    case _:
      usage()

def Command.go.if(c: Bool, +dir: String, rest: List<String>) -> IO(Unit):
  match c:
    case True{}:
      Command.national(dir, rest)
    case False{}:
      Command.times(dir, rest)

def Command.go(+cmd: String, +dir: String, rest: List<String>) -> IO(Unit):
  Command.go.if(String.eq(cmd, "national"), dir, rest)

def Command.bench(+a: String, +b: String, rest: List<String>) -> IO(Unit):
  match rest:
    case +c <> _:
      do IO<Unit>:
        +crews : Nat <- RM.Arg(a)
        +jobs : Nat <- RM.Arg(b)
        +days : Nat <- RM.Arg(c)
        run(crews, jobs, days)
    case _:
      run(100n, 1000n, 7n)

def Command.pick(c: Bool, +cmd: String, +dir: String, rest: List<String>) -> IO(Unit):
  match c:
    case True{}:
      Command.go(cmd, dir, rest)
    case False{}:
      Command.bench(cmd, dir, rest)

def start(args: List<String>) -> IO(Unit):
  match args:
    case _ <> +cmd <> +dir <> rest:
      Command.pick(Bool.or(String.eq(cmd, "national"), String.eq(cmd, "times")), cmd, dir, rest)
    case _:
      run(100n, 1000n, 7n)

def main() -> IO(Unit):
  IO.bind(List<String>, Unit, IO.args(), start)
