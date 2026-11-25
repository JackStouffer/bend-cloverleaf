import Base
import ./openapi.bend as O

# Prints openapi.json. Run `npm run gen:api` in frontend/ rather than this
# directly, so the typed client is regenerated with it.
def main() -> IO(Unit):
  IO.print(O.Spec.text())
