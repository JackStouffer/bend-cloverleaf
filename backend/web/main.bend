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
# events.log, one change per line, never rewritten, and snapshot.json, the
# store after the log's first lines. The snapshot is rewritten at startup,
# after the replay. A snapshot cut off by a crash doesn't parse, and then the
# whole log is replayed.

def Job() -> Type:
  String & Chan(String)

def Wrote() -> Type:
  File & Result<&1, &1, U32 & String, Unit>

def Bytes() -> Type:
  File & Result<&1, &1, U32 & String, List<&2, U32>>

def Next() -> Type:
  File -> St.Store -> IO(Unit)

# The store's loop
# ----------------

def saved(w: Wrote(), +c: St.Change, response: String, +store: St.Store, reply: Chan(String), next: Next()) -> IO(Unit):
  (log, outcome) = w
  match outcome:
    case Done{u}:
      do IO<Unit>:
        sent : Result<&1, &1, String, Unit> <- Chan.send(String, reply, response)
        next(log, St.Store.apply(store, c))
    case Fail{e}:
      do IO<Unit>:
        IO.print_err("cloverleaf web: the event log could not be written, so a change was refused")
        sent : Result<&1, &1, String, Unit> <- Chan.send(String, reply, Api.Api.unsaved())
        next(log, store)

def logged(change: Maybe<&2, St.Change>, response: String, log: File, +store: St.Store, reply: Chan(String), next: Next()) -> IO(Unit):
  match change:
    case None{}:
      do IO<Unit>:
        sent : Result<&1, &1, String, Unit> <- Chan.send(String, reply, response)
        next(log, store)
    case Some{+c}:
      IO.bind(Wrote(), Unit, File.write(log, St.Change.line(c)), w => saved(w, c, response, store, reply, next))

def handled(+h: Api.Handled, log: File, +store: St.Store, reply: Chan(String), next: Next()) -> IO(Unit):
  logged(Api.Handled.change(h), Api.Handled.response(h), log, store, reply, next)

def took(got: Maybe<&1, Job()>, log: File, +store: St.Store, next: Next()) -> IO(Unit):
  match got:
    case None{}:
      File.close(log)
    case Some{job}:
      (text, reply) = job
      handled(Api.Api.handle(text, store), log, store, reply, next)

def keep(fuel: Nat, log: File, store: St.Store, +jobs: Chan(Job())) -> IO(Unit):
  match fuel:
    case 0n:
      File.close(log)
    case 1n+rest:
      IO.bind(Maybe<&1, Job()>, Unit, Chan.recv(Job(), jobs),
        got => took(got, log, store, l => s => keep(rest, l, s, jobs)))

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

def whole(chunks: List<&2, List<&2, U32>>) -> List<&2, U32>:
  List.concat(&2, U32, List.reverse(&2, List<&2, U32>, chunks))

def slurp.end(f: File, chunks: List<&2, List<&2, U32>>) -> IO(List<&2, U32>):
  do IO<List<&2, U32>>:
    File.close(f)
    return whole(chunks)

def slurp.more(empty: Bool, f: File, bs: List<&2, U32>, chunks: List<&2, List<&2, U32>>, next: File -> List<&2, List<&2, U32>> -> IO(List<&2, U32>)) -> IO(List<&2, U32>):
  match empty:
    case True{}:
      slurp.end(f, chunks)
    case False{}:
      next(f, bs <> chunks)

def slurp.got(p: Bytes(), chunks: List<&2, List<&2, U32>>, next: File -> List<&2, List<&2, U32>> -> IO(List<&2, U32>)) -> IO(List<&2, U32>):
  (f, r) = p
  match r:
    case Fail{e}:
      slurp.end(f, chunks)
    case Done{+bs}:
      slurp.more(List.is_empty(&2, U32, bs), f, bs, chunks, next)

def slurp(fuel: Nat, f: File, chunks: List<&2, List<&2, U32>>) -> IO(List<&2, U32>):
  match fuel:
    case 0n:
      slurp.end(f, chunks)
    case 1n+rest:
      IO.bind(Bytes(), List<&2, U32>, File.read_bytes(f, 65536), p => slurp.got(p, chunks, g => c => slurp(rest, g, c)))

# A file's bytes, or none if it can't be opened.
def read_all.opened(r: Result<&1, &1, U32 & String, File>) -> IO(List<&2, U32>):
  match r:
    case Fail{e}:
      IO.pure(List<&2, U32>, [])
    case Done{f}:
      slurp(1000000n, f, [])

def read_all(path: String) -> IO(List<&2, U32>):
  IO.bind(Result<&1, &1, U32 & String, File>, List<&2, U32>, File.open(path, "r"), read_all.opened)

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

def wrote.close(w: Wrote()) -> IO(Unit):
  (f, r) = w
  match r:
    case Done{u}:
      File.close(f)
    case Fail{e}:
      do IO<Unit>:
        IO.print_err("cloverleaf web: the snapshot could not be written")
        File.close(f)

def snapshot.opened(o: Result<&1, &1, U32 & String, File>, text: String) -> IO(Unit):
  match o:
    case Fail{e}:
      IO.print_err("cloverleaf web: the snapshot could not be opened")
    case Done{f}:
      IO.bind(Wrote(), Unit, File.write(f, text), wrote.close)

def snapshot.write(newer: Bool, path: String, n: Nat, store: St.Store) -> IO(Unit):
  match newer:
    case True{}:
      IO.bind(Result<&1, &1, U32 & String, File>, Unit, File.open(path, "w"), o => snapshot.opened(o, St.Snapshot.text(n, store)))
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

def run(+jobs: Chan(Job()), log: File, store: St.Store) -> IO(Unit):
  do IO<Unit>:
    IO.spawn(Unit, keep(4000000000n, log, store, jobs))
    listener : Listener <- IO.try(Listener, TCP.listen("0.0.0.0", 8080))
    IO.print("cloverleaf web listening on 8080")
    serve(4000000000n, listener, jobs)

def serving(log: File, store: St.Store) -> IO(Unit):
  do IO<Unit>:
    jobs : Chan(Job()) <- Chan.new(Job(), 1024)
    run(jobs, log, store)

def mended(+dir: String, +skip: Nat, torn: Bool, +r: St.Replay) -> IO(Unit):
  do IO<Unit>:
    IO.print("cloverleaf web: " ++ Nat.show(St.Replay.lines(r)) ++ " log lines, " ++ Nat.show(skip) ++ " from the snapshot, "
      ++ Nat.show(St.Replay.bad(r)) ++ " not a change")
    log : File <- IO.try(File, File.open(dir ++ "/events.log", "a"))
    mended : File <- mend(torn, log)
    snapshot.write(Nat.is_lt(skip, St.Replay.lines(r)), dir ++ "/snapshot.json", St.Replay.lines(r), St.Replay.store(r))
    serving(mended, St.Replay.store(r))

def resumed(+dir: String, +skip: Nat, +r: St.Replay) -> IO(Unit):
  mended(dir, skip, St.Replay.torn(r), St.Replay.finish(r))

def resume(+dir: String, +skip: Nat, s: St.Store) -> IO(Unit):
  do IO<Unit>:
    r : St.Replay <- read_log(dir ++ "/events.log", St.Replay.start(skip, s))
    resumed(dir, skip, r)

def begin(+dir: String, m: Maybe<&2, St.Snap>) -> IO(Unit):
  match m:
    case None{}:
      resume(dir, 0n, St.Store.empty())
    case Some{St.Snap{n, s}}:
      resume(dir, n, s)

def start(+dir: String) -> IO(Unit):
  do IO<Unit>:
    snap : List<&2, U32> <- read_all(dir ++ "/snapshot.json")
    begin(dir, St.Snapshot.parse(U.Utf8.decode(snap)))

def data_dir(r: Result<&1, &1, U32 & String, String>) -> String:
  match r:
    case Done{d}:
      d
    case Fail{e}:
      "/data"

def main() -> IO(Unit):
  do IO<Unit>:
    env : Result<&1, &1, U32 & String, String> <- IO.get_env("CLOVERLEAF_DATA")
    start(data_dir(env))
