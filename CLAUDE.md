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
node scripts/fetch-road-data.mjs                          # download the US .pbf and state outlines to data/osm
node scripts/road-build.mjs data/osm/us-latest.osm.pbf data/osm/outlines data/road  # build per-state road records
node scripts/check-road-data.mjs data/road                # check the output against its format
node --test "scripts/*.test.mjs"                         # test the Node scripts
node scripts/check-road-matrix.mjs check data/road/texas points.bin matrix.bin 36000  # compare a matrix with a separate implementation
docker compose run --rm road-build                       # fetch and build the road data in Compose, once Docker is here
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
bend road/main.bend -o build/road                                    # build the road process
./build/road +RTS --threads 12 -RTS bench ../data/road/texas 100 36000 2                     # searches, limit, lane depth
./build/road +RTS --threads 12 -RTS matrix ../data/road/texas points.bin matrix.bin 36000 2  # points, output, limit, lane depth
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
- Contractors never work across a state line. An `Instance` is one state, so overflow can't leave it, and the national solve is one independent instance per state.
- Slow pure work blocks the whole event loop, so heavy work never runs in the web process. Web, solver and road lookups are separate processes.
- Use `Nat` fuel for long-running loops, with a continuation for the next step, as in `backend/web/main.bend`. This passes the proof gate, so use `@unsafe` only when fuel can't work, and only in the IO shell.
- nginx is the only public entry point. It handles TLS and static files, and backend services stay on the internal Docker network.
- Keep local setup matching a real deployment. Don't add dev-only shortcuts that skip nginx or TLS.
- Each process gets its own Compose service. Secrets come from a gitignored `.env` file, never from images or Compose files.
- The backend is all Bend, except `scripts/road-build.mjs`, which decodes the `.pbf` before deploy. The app never runs it. Ask before adding an outside backend dependency or a C effect, because foreign code fails `--verdict`.
- Don't add Python. Any supporting script is written for Node.js, which the frontend already needs.
- The frontend is TypeScript and Preact in `frontend/`. Keep it strict: no `any`, no lint suppressions to get a check passing, and zero ESLint warnings.
- The Bend route table is the single source of truth for the API. Change the route table, then run `npm run gen:api`. Never hand-edit `openapi.json` or the generated types.
- The frontend calls the API only through the generated client, apart from the typed Server-Sent Events wrapper.
- Bend's JS target runs sequentially, so don't plan on parallel work in the browser.

## Data and performance

- Keep large data in `Array<U32>` (about 4 bytes per slot) or fixed-size records. Lists cost a cell per element and `String` about 24 bytes per character, so convert early.
- `File.size` fails above 4GB and `File.read_at` takes a `U32` offset. Keep runtime data files under 4GB. Sequential reads work past 4GB.
- The whole stack must run in 8GB, even though this machine has 15GB. Each service has a hard cap, listed in PLAN.md. Test against it with `systemd-run --user --scope -q -p MemoryMax=2G -p MemorySwapMax=0 <command>`.
- Never load the whole road network into RAM. Stream it, or load one state at a time.
- Each search lane copies the state's graph, so set lanes from the state's size. Texas fits 4 lanes under the 1GB `road` cap, not 8.
- Bend's heap never shrinks, and freed memory is reused only at the same power-of-two size, so peak use per size lasts until exit. Use fixed-size arrays, reuse them, and give each batch pass its own process.
- Bend has no heap limit, so going over a cap gets the process killed with no error, and with no cap a bad size can reboot the whole machine. Size every buffer and batch up front, and check any size that comes from outside before allocating.
- Run compiled Bend under `systemd-run --user --scope -q -p MemoryMax=... -p MemorySwapMax=0`. Delete the old binary before rebuilding and use `set -o pipefail`, because `bend ... | tail` hides a failed build and leaves a stale binary to run.
- Read files in small chunks and consume them as they arrive. Holding whole files as `List`s is about 4x slower and costs 16 bytes per byte.
- `U32` is the widest integer in Base and it wraps silently. Check for overflow in totals and offsets, and remember that OSM node IDs need more than 32 bits.
- Parallel calls need balanced work, because tasks are never moved once assigned. Split by estimated cost, not by count.
- A fork tree must end in a parallel call to a def that never forks. A def that can fork runs while the tree grows, on a couple of threads, even in its base case, so leaves wait for each other.
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
- An unsafe IO loop split across two defs can pass the checker and then fail in clang with an undeclared `spin_N`. Use one recursive def with pure helpers.
- A pair from a computed value can't be destructured in the same def, so each array read needs its own helper def.
- State laws in plain numbers, not through the helper being tested, or a bug in the helper changes the law with it.
- A proof can't use an array twice and dead evidence doesn't count. `copy` and `reads` in `proof/road.bend` hand back live copies with evidence, so use those.
- Each array read in a hot loop can be one mode of a single `Nat`-fuel def, with the read's pair as a parameter. It compiles to a flat loop, as `road/search.bend` shows.
- `+` on a field of a dependent pair fails with "cannot infer". Pass the field to a helper with a `+` parameter.

## Benchmarks

- The compiler can collapse simple arithmetic loops, so use a workload it can't simplify, and distrust results that look too fast.
- When testing whether one request blocks another, confirm the slow job is still running when the second request arrives.
- Use a real load generator. Spawning `curl` in a loop measures `curl`.

## Scorecard

Keep the scorecard from PLAN.md current as work happens. Log missing features, confusing errors, `@unsafe` use, proof effort, and bugs that proofs caught or missed.
