import Base
import ./routes.bend as Routes

def sent(result: Socket & Result<&1, &1, (U32 & String) & List<&2, U32>, Unit>) -> IO(Unit):
  (socket, outcome) = result
  Socket.close(socket)

def answer(socket: Socket, request: Maybe<&1, String>) -> IO(Unit):
  match request:
    case None{}:
      Socket.close(socket)
    case Some{text}:
      IO.bind(Socket & Result<&1, &1, (U32 & String) & List<&2, U32>, Unit>, Unit,
        TCP.send(socket, Routes.route(text)), sent)

def received(result: Socket & Result<&1, &1, U32 & String, Maybe<&1, String>>) -> IO(Unit):
  (socket, outcome) = result
  match outcome:
    case Fail{error}:
      Socket.close(socket)
    case Done{request}:
      answer(socket, request)

def handle(socket: Socket) -> IO(Unit):
  IO.bind(Socket & Result<&1, &1, U32 & String, Maybe<&1, String>>, Unit,
    TCP.recv(socket, 65536), received)

def accepted(result: Listener & Result<&1, &1, U32 & String, Socket>, next: Listener -> IO(Unit)) -> IO(Unit):
  (listener, outcome) = result
  match outcome:
    case Fail{error}:
      next(listener)
    case Done{socket}:
      do IO<Unit>:
        IO.spawn(Unit, handle(socket))
        next(listener)

# Fuel bounds the loop for the termination check. When it runs out the process
# exits and Compose restarts it.
def serve(fuel: Nat, listener: Listener) -> IO(Unit):
  match fuel:
    case 0n:
      IO.pure(Unit, Unit{})
    case 1n+rest:
      IO.bind(Listener & Result<&1, &1, U32 & String, Socket>, Unit,
        TCP.accept(listener), result => accepted(result, next => serve(rest, next)))

def main() -> IO(Unit):
  do IO<Unit>:
    listener : Listener <- IO.try(Listener, TCP.listen("0.0.0.0", 8080))
    IO.print("cloverleaf web listening on 8080")
    serve(4000000000n, listener)
