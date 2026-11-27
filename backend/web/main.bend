import Base
import ./api.bend as Api
import ./store.bend as St
import ./utf8.bend as U

# The web process. One computation owns the store and the log: connections
# hand it their request over a channel and wait for the response, so changes
# are applied one at a time in log order. A change is written to the log
# before its response is sent, so a reply the client saw survives a crash.
#
# The data directory comes from CLOVERLEAF_DATA, /data by default. It holds
# events.log, one change per line, never rewritten, and snapshot.jsonl, the
# store after the log's first lines. The snapshot is rewritten at startup,
# after the replay. Both are read and written a line at a time, so neither is
# ever held whole. A snapshot cut off by a crash doesn't load, and then the
# whole log is replayed.
#
# CLOVERLEAF_ADMIN_KEY, from the gitignored .env, is the key that adds dealer
# organizations. The process keeps only its hash. Without one, nobody is the
# admin. A request to add an organization gets 32 bytes from /dev/urandom,
# which its API key is made from. Other requests read none.

def Job() -> Type:
  String & Chan(String)

def Wrote() -> Type:
  File & Result<&1, &1, U32 & String, Unit>

def Bytes() -> Type:
  File & Result<&1, &1, U32 & String, List<&2, U32>>

# The log handle, whether a write failed partway and may have left a torn line,
# and the store.
def Next() -> Type:
  File -> Bool -> St.Store -> IO(Unit)

# The store's loop
# ----------------

def saved(w: Wrote(), +c: St.Change, response: String, +store: St.Store, reply: Chan(String), next: Next()) -> IO(Unit):
  (log, outcome) = w
  match outcome:
    case Done{u}:
      do IO<Unit>:
        sent : Result<&1, &1, String, Unit> <- Chan.send(String, reply, response)
        next(log, False{}, St.Store.apply(store, c))
    case Fail{e}:
      do IO<Unit>:
        IO.print_err("cloverleaf web: the event log could not be written, so a change was refused")
        sent : Result<&1, &1, String, Unit> <- Chan.send(String, reply, Api.Api.unsaved())
        next(log, True{}, store)

def logged(change: Maybe<&2, St.Change>, response: String, log: File, torn: Bool, +store: St.Store, reply: Chan(String), next: Next()) -> IO(Unit):
  match change:
    case None{}:
      do IO<Unit>:
        sent : Result<&1, &1, String, Unit> <- Chan.send(String, reply, response)
        next(log, torn, store)
    case Some{+c}:
      IO.bind(Wrote(), Unit, File.write(log, St.Change.line.after(torn, c)), w => saved(w, c, response, store, reply, next))

def handled(+h: Api.Handled, log: File, torn: Bool, +store: St.Store, reply: Chan(String), next: Next()) -> IO(Unit):
  logged(Api.Handled.change(h), Api.Handled.response(h), log, torn, store, reply, next)

def seed.bytes(got: Result<&1, &1, U32 & String, List<&2, U32>>) -> List<&2, U32>:
  match got:
    case Done{bs}:
      bs
    case Fail{e}:
      []

def seeded(p: Bytes(), text: String, reply: Chan(String), log: File, torn: Bool, +store: St.Store, admin: Maybe<&2, String>, next: Next()) -> IO(Unit):
  (f, got) = p
  do IO<Unit>:
    File.close(f)
    handled(Api.Api.handle(text, store, admin, seed.bytes(got)), log, torn, store, reply, next)

# A request that can't read the random bytes still gets an answer: one that
# needs a new key is refused.
def seed.opened(o: Result<&1, &1, U32 & String, File>, text: String, reply: Chan(String), log: File, torn: Bool, +store: St.Store, admin: Maybe<&2, String>, next: Next()) -> IO(Unit):
  match o:
    case Fail{e}:
      handled(Api.Api.handle(text, store, admin, []), log, torn, store, reply, next)
    case Done{f}:
      IO.bind(Bytes(), Unit, File.read_bytes(f, 32), p => seeded(p, text, reply, log, torn, store, admin, next))

def seed.wanted(want: Bool, +text: String, reply: Chan(String), log: File, torn: Bool, +store: St.Store, admin: Maybe<&2, String>, next: Next()) -> IO(Unit):
  match want:
    case True{}:
      IO.bind(Result<&1, &1, U32 & String, File>, Unit, File.open("/dev/urandom", "r"),
        o => seed.opened(o, text, reply, log, torn, store, admin, next))
    case False{}:
      handled(Api.Api.handle(text, store, admin, []), log, torn, store, reply, next)

def seed.chosen(+text: String, reply: Chan(String), log: File, torn: Bool, +store: St.Store, admin: Maybe<&2, String>, next: Next()) -> IO(Unit):
  seed.wanted(Api.Api.needs_seed(text), text, reply, log, torn, store, admin, next)

def took(got: Maybe<&1, Job()>, log: File, torn: Bool, +store: St.Store, admin: Maybe<&2, String>, next: Next()) -> IO(Unit):
  match got:
    case None{}:
      File.close(log)
    case Some{job}:
      (text, reply) = job
      seed.chosen(text, reply, log, torn, store, admin, next)

def keep(fuel: Nat, log: File, torn: Bool, store: St.Store, +admin: Maybe<&2, String>, +jobs: Chan(Job())) -> IO(Unit):
  match fuel:
    case 0n:
      File.close(log)
    case 1n+rest:
      IO.bind(Maybe<&1, Job()>, Unit, Chan.recv(Job(), jobs),
        got => took(got, log, torn, store, admin, l => t => s => keep(rest, l, t, s, admin, jobs)))

# Connections
# -----------

def sent(result: Socket & Result<&1, &1, (U32 & String) & List<&2, U32>, Unit>) -> IO(Unit):
  (socket, outcome) = result
  Socket.close(socket)

def answer(socket: Socket, response: Maybe<&1, String>) -> IO(Unit):
  match response:
    case None{}:
      Socket.close(socket)
    case Some{text}:
      IO.bind(Socket & Result<&1, &1, (U32 & String) & List<&2, U32>, Unit>, Unit,
        TCP.send(socket, text), sent)

def asked(+reply: Chan(String), socket: Socket, text: String, jobs: Chan(Job())) -> IO(Unit):
  do IO<Unit>:
    put : Result<&1, &1, Job(), Unit> <- Chan.send(Job(), jobs, (text, reply))
    got : Maybe<&1, String> <- Chan.recv(String, reply)
    answer(socket, got)

def respond(socket: Socket, bytes: List<&2, U32>, jobs: Chan(Job())) -> IO(Unit):
  do IO<Unit>:
    reply : Chan(String) <- Chan.new(String, 1)
    asked(reply, socket, U.Utf8.decode(bytes), jobs)

def Recv() -> Type:
  Socket & Result<&1, &1, U32 & String, Maybe<&1, List<&2, U32>>>

def received(r: Recv(), bytes: List<&2, U32>, jobs: Chan(Job()), next: Socket -> List<&2, U32> -> IO(Unit)) -> IO(Unit):
  (socket, outcome) = r
  match outcome:
    case Fail{error}:
      Socket.close(socket)
    case Done{None{}}:
      respond(socket, bytes, jobs)
    case Done{Some{chunk}}:
      next(socket, List.append(&2, U32, bytes, chunk))

def more(ready: Bool, socket: Socket, bytes: List<&2, U32>, jobs: Chan(Job()), next: Socket -> List<&2, U32> -> IO(Unit)) -> IO(Unit):
  match ready:
    case True{}:
      respond(socket, bytes, jobs)
    case False{}:
      IO.bind(Recv(), Unit, TCP.recv_bytes(socket, 65536), r => received(r, bytes, jobs, next))

# Reads until the request is whole, or the fuel runs out. nginx caps a body
# at 1MB, and 24 reads of 64KB cover that and the headers.
def reading(fuel: Nat, socket: Socket, +bytes: List<&2, U32>, +jobs: Chan(Job())) -> IO(Unit):
  match fuel:
    case 0n:
      respond(socket, bytes, jobs)
    case 1n+rest:
      more(Api.Http.ready(bytes), socket, bytes, jobs, s => b => reading(rest, s, b, jobs))

def accepted(result: Listener & Result<&1, &1, U32 & String, Socket>, +jobs: Chan(Job()), next: Listener -> IO(Unit)) -> IO(Unit):
  (listener, outcome) = result
  match outcome:
    case Fail{error}:
      next(listener)
    case Done{socket}:
      do IO<Unit>:
        IO.spawn(Unit, reading(24n, socket, [], jobs))
        next(listener)

# Fuel bounds the loop for the termination check. When it runs out the process
# exits and Compose restarts it.
def serve(fuel: Nat, listener: Listener, +jobs: Chan(Job())) -> IO(Unit):
  match fuel:
    case 0n:
      IO.pure(Unit, Unit{})
    case 1n+rest:
      IO.bind(Listener & Result<&1, &1, U32 & String, Socket>, Unit,
        TCP.accept(listener), result => accepted(result, jobs, next => serve(rest, next, jobs)))

# Startup
# -------

def replay.end(f: File, r: St.Replay) -> IO(St.Replay):
  do IO<St.Replay>:
    File.close(f)
    return r

def replay.more(empty: Bool, f: File, bs: List<&2, U32>, r: St.Replay, next: File -> St.Replay -> IO(St.Replay)) -> IO(St.Replay):
  match empty:
    case True{}:
      replay.end(f, r)
    case False{}:
      next(f, St.Replay.feed(bs, r))

def replay.got(p: Bytes(), r: St.Replay, next: File -> St.Replay -> IO(St.Replay)) -> IO(St.Replay):
  (f, got) = p
  match got:
    case Fail{e}:
      replay.end(f, r)
    case Done{+bs}:
      replay.more(List.is_empty(&2, U32, bs), f, bs, r, next)

# Folds the log into the replay a chunk at a time, so the log is never held
# whole.
def replay(fuel: Nat, f: File, r: St.Replay) -> IO(St.Replay):
  match fuel:
    case 0n:
      replay.end(f, r)
    case 1n+rest:
      IO.bind(Bytes(), St.Replay, File.read_bytes(f, 65536), p => replay.got(p, r, g => s => replay(rest, g, s)))

def read_log.opened(o: Result<&1, &1, U32 & String, File>, r: St.Replay) -> IO(St.Replay):
  match o:
    case Fail{e}:
      IO.pure(St.Replay, r)
    case Done{f}:
      replay(100000000n, f, r)

def read_log(path: String, r: St.Replay) -> IO(St.Replay):
  IO.bind(Result<&1, &1, U32 & String, File>, St.Replay, File.open(path, "r"), o => read_log.opened(o, r))

# The snapshot, read a chunk at a time.
def load.end(f: File, l: St.Load) -> IO(St.Load):
  do IO<St.Load>:
    File.close(f)
    return l

def load.more(empty: Bool, f: File, bs: List<&2, U32>, l: St.Load, next: File -> St.Load -> IO(St.Load)) -> IO(St.Load):
  match empty:
    case True{}:
      load.end(f, l)
    case False{}:
      next(f, St.Load.feed(bs, l))

def load.got(p: Bytes(), l: St.Load, next: File -> St.Load -> IO(St.Load)) -> IO(St.Load):
  (f, got) = p
  match got:
    case Fail{e}:
      load.end(f, St.Load.broken())
    case Done{+bs}:
      load.more(List.is_empty(&2, U32, bs), f, bs, l, next)

def load(fuel: Nat, f: File, l: St.Load) -> IO(St.Load):
  match fuel:
    case 0n:
      load.end(f, St.Load.broken())
    case 1n+rest:
      IO.bind(Bytes(), St.Load, File.read_bytes(f, 65536), p => load.got(p, l, g => m => load(rest, g, m)))

def read_snapshot.opened(o: Result<&1, &1, U32 & String, File>) -> IO(St.Load):
  match o:
    case Fail{e}:
      IO.pure(St.Load, St.Load.start())
    case Done{f}:
      load(100000000n, f, St.Load.start())

def read_snapshot(path: String) -> IO(St.Load):
  IO.bind(Result<&1, &1, U32 & String, File>, St.Load, File.open(path, "r"), read_snapshot.opened)

# The snapshot, written a line at a time.
def snap.next(w: Wrote(), next: File -> IO(Unit)) -> IO(Unit):
  (f, r) = w
  match r:
    case Done{u}:
      next(f)
    case Fail{e}:
      do IO<Unit>:
        IO.print_err("cloverleaf web: the snapshot could not be written")
        File.close(f)

def snap.recs(fuel: Nat, f: File, rs: List<&2, St.Rec>) -> IO(Unit):
  match fuel rs:
    case 0n _:
      File.close(f)
    case 1n+k Nil{}:
      File.close(f)
    case 1n+k Con{r, rest}:
      IO.bind(Wrote(), Unit, File.write(f, St.Rec.line(r)), w => snap.next(w, g => snap.recs(k, g, rest)))

# The organizations, then the records.
def snap.orgs(fuel: Nat, f: File, gs: List<&2, St.Org>, +rs: List<&2, St.Rec>) -> IO(Unit):
  match fuel gs:
    case 0n _:
      snap.recs(List.length(&2, St.Rec, rs), f, rs)
    case 1n+k Nil{}:
      snap.recs(List.length(&2, St.Rec, rs), f, rs)
    case 1n+k Con{g, rest}:
      IO.bind(Wrote(), Unit, File.write(f, St.Org.line(g)), w => snap.next(w, h => snap.orgs(k, h, rest, rs)))

def snapshot.opened(o: Result<&1, &1, U32 & String, File>, head: String, +gs: List<&2, St.Org>, rs: List<&2, St.Rec>) -> IO(Unit):
  match o:
    case Fail{e}:
      IO.print_err("cloverleaf web: the snapshot could not be opened")
    case Done{f}:
      IO.bind(Wrote(), Unit, File.write(f, head), w => snap.next(w, g => snap.orgs(List.length(&2, St.Org, gs), g, gs, rs)))

def snapshot.write(newer: Bool, path: String, n: Nat, +store: St.Store) -> IO(Unit):
  match newer:
    case True{}:
      IO.bind(Result<&1, &1, U32 & String, File>, Unit, File.open(path, "w"), o => snapshot.opened(o, St.Snapshot.head(n, store), List.append(&2, St.Org, St.Store.orgs(store), St.Store.retired(store)), St.Store.recs(store)))
    case False{}:
      IO.pure(Unit, Unit{})

def mend.done(w: Wrote()) -> IO(File):
  (f, r) = w
  IO.pure(File, f)

# A torn last line gets its newline, so the next change starts a line of its
# own and the torn one stays a bad line.
def mend(torn: Bool, log: File) -> IO(File):
  match torn:
    case True{}:
      IO.bind(Wrote(), File, File.write(log, "\n"), mend.done)
    case False{}:
      IO.pure(File, log)

def run(+jobs: Chan(Job()), log: File, store: St.Store, admin: Maybe<&2, String>) -> IO(Unit):
  do IO<Unit>:
    IO.spawn(Unit, keep(4000000000n, log, False{}, store, admin, jobs))
    listener : Listener <- IO.try(Listener, TCP.listen("0.0.0.0", 8080))
    IO.print("cloverleaf web listening on 8080")
    serve(4000000000n, listener, jobs)

def serving(log: File, store: St.Store, admin: Maybe<&2, String>) -> IO(Unit):
  do IO<Unit>:
    jobs : Chan(Job()) <- Chan.new(Job(), 1024)
    run(jobs, log, store, admin)

def mended(+dir: String, +skip: Nat, torn: Bool, +r: St.Replay, admin: Maybe<&2, String>) -> IO(Unit):
  do IO<Unit>:
    IO.print("cloverleaf web: " ++ Nat.show(St.Replay.lines(r)) ++ " log lines, " ++ Nat.show(skip) ++ " from the snapshot, "
      ++ Nat.show(St.Replay.bad(r)) ++ " not a change")
    log : File <- IO.try(File, File.open(dir ++ "/events.log", "a"))
    mended : File <- mend(torn, log)
    snapshot.write(Nat.is_lt(skip, St.Replay.lines(r)), dir ++ "/snapshot.jsonl", St.Replay.lines(r), St.Replay.store(r))
    serving(mended, St.Replay.store(r), admin)

def resumed(+dir: String, +skip: Nat, +r: St.Replay, admin: Maybe<&2, String>) -> IO(Unit):
  mended(dir, skip, St.Replay.torn(r), St.Replay.finish(r), admin)

def resume(+dir: String, +skip: Nat, s: St.Store, admin: Maybe<&2, String>) -> IO(Unit):
  do IO<Unit>:
    r : St.Replay <- read_log(dir ++ "/events.log", St.Replay.start(skip, s))
    resumed(dir, skip, r, admin)

def begin(+dir: String, m: Maybe<&2, St.Snap>, admin: Maybe<&2, String>) -> IO(Unit):
  match m:
    case None{}:
      resume(dir, 0n, St.Store.empty(), admin)
    case Some{St.Snap{n, s}}:
      resume(dir, n, s, admin)

def start(+dir: String, admin: Maybe<&2, String>) -> IO(Unit):
  do IO<Unit>:
    snap : St.Load <- read_snapshot(dir ++ "/snapshot.jsonl")
    begin(dir, St.Load.finish(snap), admin)

def data_dir(r: Result<&1, &1, U32 & String, String>) -> String:
  match r:
    case Done{d}:
      d
    case Fail{e}:
      "/data"

def admin.key(r: Result<&1, &1, U32 & String, String>) -> Maybe<&2, String>:
  match r:
    case Done{k}:
      Api.Api.admin(k)
    case Fail{e}:
      None{}

def admin.warn(m: Maybe<&2, String>) -> IO(Unit):
  match m:
    case Some{h}:
      IO.pure(Unit, Unit{})
    case None{}:
      IO.print_err("cloverleaf web: CLOVERLEAF_ADMIN_KEY is unset, or isn't at least 32 printable ASCII characters with no spaces, so no organization can be added")

def admin.then(+admin: Maybe<&2, String>, dir: String) -> IO(Unit):
  do IO<Unit>:
    admin.warn(admin)
    start(dir, admin)

def main() -> IO(Unit):
  do IO<Unit>:
    env : Result<&1, &1, U32 & String, String> <- IO.get_env("CLOVERLEAF_DATA")
    key : Result<&1, &1, U32 & String, String> <- IO.get_env("CLOVERLEAF_ADMIN_KEY")
    admin.then(admin.key(key), data_dir(env))
