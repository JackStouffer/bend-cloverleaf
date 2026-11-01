# Cloverleaf

Cloverleaf plans daily routes for about 1,000 auto appraisal contractors across the lower 48. It's also a proof of concept for whether Bend works for general-purpose web programming, so record friction honestly instead of working around it quietly.

[PLAN.md](PLAN.md) holds the requirements, architecture, milestones and proof scope. Read it before starting work, and keep it updated when a decision changes.

## Public code

The code here will be published publicly, so it must not include any secrets, envs or passwords. That covers commits, tests, fixtures, logs, docs and config examples.

## Local Development

All work is done in main. No need to go through branching/pull request formalities. 

## Bend rules

- Run `bend guide` to learn Bend before writing it. Also read `bend guide effects` before writing an effect, and `bend guide shaders` before writing parallel code.
- Use `LAWS.bend` to keep important rules.
- Run `bend PROOF.bend` before committing. It must print ALL PROOFS CHECK.
- Keep rules the laws can't state in `test/scenario.bend`, and run it before committing too.
- Parallelize the code whenever possible.

## Commands

Run the app from the repo root. Everything goes through nginx at https://localhost:8443, including local development and testing, so don't call the backend directly.

```bash
docker compose up --build                                # real-world run with the built frontend
docker compose -f compose.yaml -f compose.dev.yaml watch # development with hot reload
```

Run these from `backend/`, and write build output to `backend/build/`:

```bash
bend PROOF.bend                       # the proof gate
bend PROOF.bend --verdict             # recheck with the proven kernel
bend file.bend --check-only           # check without running
bend file.bend -o build/out           # build a native binary
./build/out +RTS --threads 12 -RTS    # run on 12 CPU threads
bend file.bend -o file.mjs            # build an ES module of non-IO defs for the frontend
bend base Map                         # look up a name in Base
bend test/scenario.bend -o build/scenario && ./build/scenario        # concrete scenarios
bend solver/main.bend -o build/solver                                # build the benchmark
./build/solver +RTS --threads 4 -RTS 1000 10000 7                    # crews, jobs, days
```

Run these from `frontend/`, on Node 24:

```bash
npm run check                         # types, lint and format, plus tests and spec drift when added
npm run gen:api                       # regenerate openapi.json and the typed client, once added
```

## Laws and proofs

- `LAWS.bend` states the rules and `PROOF.bend` proves them, with `def Laws.name` for `law name`.
- Never weaken, delete or reword an existing law to get a proof through. If a law seems wrong, stop and ask.
- New business rules go in as laws when they can be stated over the pure core. The more rules to formalize business logic, the better
- `PROOF.bend` must not import IO code. A `@unsafe` or foreign def anywhere in its imports makes the gate fail.
- Prove that plans are valid. Measure route quality with benchmarks, since optimality isn't a proof goal.

## Architecture rules

- Keep pure logic and IO in separate modules, with as little logic in the IO shell as possible.
- Slow pure work blocks the whole event loop, so heavy work never runs in the web process. Web, solver and road lookups are separate processes.
- Use `Nat` fuel for long-running loops, with a continuation for the next step, as in `backend/web/main.bend`. This passes the proof gate, so use `@unsafe` only when fuel can't work, and only in the IO shell.
- nginx is the only public entry point. It handles TLS and static files, and backend services stay on the internal Docker network.
- Keep local setup matching a real deployment. Don't add dev-only shortcuts that skip nginx or TLS.
- Each process gets its own Compose service. Secrets come from a gitignored `.env` file, never from images or Compose files.
- The backend is all Bend. Ask before adding an outside backend dependency or a C effect, because foreign code fails `--verdict`.
- The frontend is TypeScript and Preact in `frontend/`. Keep it strict: no `any`, no lint suppressions to get a check passing, and zero ESLint warnings.
- The Bend route table is the single source of truth for the API. Change the route table, then run `npm run gen:api`. Never hand-edit `openapi.json` or the generated types.
- The frontend calls the API only through the generated client, apart from the typed Server-Sent Events wrapper.
- Bend's JS target runs sequentially, so don't plan on parallel work in the browser.

## Data and performance

- Keep large data in `Array<U32>` (about 4 bytes per slot) or fixed-size records. Lists cost a cell per element and `String` about 24 bytes per character, so convert early.
- `File.size` fails above 4GB and `File.read_at` takes a `U32` offset. Keep runtime data files under 4GB. Sequential reads work past 4GB.
- Never load the whole road network into RAM. This machine has 15GB, and data should be streamed or loaded by region.
- `U32` is the widest integer in Base and it wraps silently. Check for overflow in totals and offsets, and remember that OSM node IDs need more than 32 bits.
- Parallel calls need balanced work, because tasks are never moved once assigned. Split by estimated cost, not by count.
- When cost can't be estimated, fork far more tasks than cores, and sweep the fork depth rather than guessing it.
- Values marked `+` and read by every lane cost an atomic per read.
- This machine can't build GPU code, and `!` builds silently produce no `.gpu` file. Don't use `!`.

## Bend gotchas

- There's no `if`, so use `match` on `True{}` and `False{}`.
- `match` works only on parameters or pattern-bound variables. To match a computed value, pass it to a helper.
- `do` blocks don't accept tuple destructuring as a statement. Bind the pair, then pass it to a helper.
- Variables are single-use by default. Mark a parameter `+` to reuse it, which requires a `Data` type.
- Mutual recursion is banned for checked defs.
- `def f?(..)` declares an unsafe def, but it's called as `f(..)`.
- A `Nat` parameter that shrinks must come before arguments that change in recursive calls.
- `Nat` is a 48-bit immediate with O(1) arithmetic that traps on overflow, so prefer it to `U32` for domain numbers.
- `%e : P` with `e : {a == b : T}` replaces `b` in the goal with `a`. Use `Equal.sym` to go the other way.
- A for-all hypothesis is an affine closure and can only be used once. State it as a `Bool` over a list, because equality proofs are `Data`.
- A literal fuel inside a def can hang the checker with no message. Pass fuel as a parameter to anything a law mentions.
- State laws in plain numbers, not through the helper being tested, or a bug in the helper changes the law with it.

## Benchmarks

- The compiler can collapse simple arithmetic loops, so use a workload it can't simplify, and distrust results that look too fast.
- When testing whether one request blocks another, confirm the slow job is still running when the second request arrives.
- Use a real load generator. Spawning `curl` in a loop measures `curl`.

## Scorecard

Keep the scorecard from PLAN.md current as work happens. Log missing features, confusing errors, `@unsafe` use, proof effort, and bugs that proofs caught or missed.
