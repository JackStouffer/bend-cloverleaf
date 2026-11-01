import Base

def json(status: String, body: String) -> String:
  "HTTP/1.1 " ++ status ++ "\r\nConnection: close\r\nContent-Type: application/json\r\n\r\n" ++ body

def respond(found: Bool) -> String:
  match found:
    case True{}:
      json("200 OK", "{\"status\":\"ok\"}")
    case False{}:
      json("404 Not Found", "{\"error\":\"not_found\"}")

def route(request: String) -> String:
  respond(String.starts_with(request, "GET /api/health "))
