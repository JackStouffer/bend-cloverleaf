# Cloverleaf: Milestone Plan

Cloverleaf is a proof of concept that tests whether Bend works for general-purpose web programming. It's a full working app that plans daily routes for about 1,000 auto appraisal contractors across the lower 48.

## What we're building

- **Requests:** dealers send appraisals through an external API or the web app, and individuals book through a web form. Either can cancel.
- **Planning:** a nightly national solve assigns each appraisal to a contractor and orders each route as a loop from that contractor's daily start point and back.
- **Same-day changes:** new requests, cancellations and failed stops repair routes during the day.
- **Views:** admins, requesters and contractors each get their own view, with live updates.

### Agreed requirements

| Area | Decision |
|---|---|
| Assignment | The optimizer chooses the contractor. Overlapping zips are candidates |
| Volume | 5,000-10,000 appraisals per day, about 20 minutes each |
| Deadlines | Complete by a date, so work can move between days |
| Priorities | Meet deadlines first, then balance work across contractors |
| Contractor limits | Max hours per day and an availability calendar |
| Overflow | Go outside assigned zips automatically, only to save a deadline, with a cap on extra drive time and a flag for admins |
| Healing | Reorder the route, then backfill from neighbors or later days |
| Contractor app | Route and navigation, status reporting, availability, live location |
| Booking | Web form with a required-by date, then tracking and cancellation by private link |
| Notifications | In-app live updates only |
| Auth | Email and password for people, API keys for organizations |
| Road data | OpenStreetMap, handled entirely in Bend, including reading the raw `.pbf` |
| Geocoding | OpenStreetMap plus Census TIGER, self-hosted |
| Backend | Bend |
| Frontend | TypeScript and Preact, in a real npm project with strict type checking, strict ESLint and Prettier |
| API contract | Bend generates the OpenAPI spec, and the frontend uses a typed client generated from it |
| Data | Realistic synthetic data |
| Hosting | Local machine only, run with Docker Compose in the same shape as a real deployment |
| TLS | Bend has no TLS, so nginx terminates it in front of the backend |
| Repository | Separate `backend/` and `frontend/` folders |
| Scope ends at | Appraisal marked complete. No report or photo workflow |

### Assumptions to correct if wrong

- Planning covers a rolling 7 days. The next day's routes are published after the nightly solve.
- Deadlines mean end of day in the appraisal's local time zone.
- Drive times come from road type and speed limits, with no live traffic.
- Stops that are completed or underway are locked during healing, and form the front of the route.
- A cancellation is refused once the stop is underway, because a locked stop can't leave its route.
- Out-of-zip work is capped at 60 extra drive minutes by default, and admins can change this. The cap counts unlocked out-of-zip stops only. Without that exception a cancellation next to a locked out-of-zip stop could push a route over the cap with no way to heal it.
- A failed stop goes straight back to the backlog, which is what retries it.
- A sick contractor's route closes to new work and its open stops go to the backlog. Updating the calendar itself is left to Milestone 6.
- A dealer's opening hours and an individual's presence at home aren't modeled, because deadlines are date-only.
- The external API is versioned REST with JSON, and creating a request is safe to retry.
- Password resets are done by an admin, because there's no email.
- An individual's tracking link is shown only at booking, for the same reason.
- The browser map uses free public base-map tiles, with route lines drawn from our own road data.

## Measured constraints

Tested on Bend 2.0.39 on this machine (6 cores, 12 threads, 15GB RAM, 926GB free disk).

| Finding | Effect on the design |
|---|---|
| A slow pure job blocks every other request. A trivial request waited 1.41s on 1 thread | Web, solver and road lookups must be separate processes |
| Balanced CPU work scaled 8.5x on 12 threads | The parallel approach is sound, though real solver work still has to prove it |
| About 8,600 small requests per second, with flat memory over 100k requests | Plenty for this API on a simple path. Retest with real handlers |
| `File.size` failed on a 5GB file, and `read_at` takes a `U32` offset | Runtime data files must stay under 4GB, so sharding is required |
| Sequential reads passed 4GB at about 285MB/s with flat 19MB memory (sparse file, 1MB chunks) | The raw `.pbf` can be streamed without loading it all |
| `Array<U32>` costs about 4 bytes per slot. A byte read as a `List` takes one cell, and `String` about 24 bytes per character | Keep large data in arrays or fixed-size records, and convert from lists quickly |
| No U64 in Base, and OSM node IDs no longer fit in 32 bits | IDs need a two-word type, or a remap to compact IDs |
| No HTTP, JSON, crypto, gzip or database in Base | All of these get built in Bend |
| No TLS in Bend | nginx handles it |
| A TCP server with `Nat` fuel passed `ALL PROOFS CHECK` with no `@unsafe`, and 4 billion fuel used only 2MB of memory | The IO shell can stay inside the proof gate, and a server needs no unsafe loop |
| Bend builds from the pinned release tarball with an empty `HOME`, and a failed `--check-only` exits non-zero | A Docker build can fail on bad Bend code |
| Bend's JS target runs sequentially | Fine for the browser validator, but no solving in the browser |
| GPU build produced no `.gpu` file here (no CUDA, clang 18) | CPU only. GPU is out of scope |
| A schema defined as a Bend datatype can set a handler's type, and a handler with a wrong field type failed to compile | API routes are defined as Bend data, so the schema is the single source of truth |
| Bend proved that encoded output always conforms to its schema, on a small schema with strings, numbers, lists and objects | Conformance is a realistic law, not just a hope |
| Bend emitted valid OpenAPI 3.1 that `openapi-typescript` and `openapi-fetch` accepted. `tsc` rejected a misspelled request field and an unknown response field | The contract chain works end to end on one route |
| A Bend module built with `-o .mjs` bundled through Vite into a Preact app under strict `tsc`, using a hand-written declaration file | The proven checker can run in the real frontend build |
| Node 18.19.1 from apt can't run `openapi-typescript`. Node 24.22.2 can | Node 24 is the project version, in `~/.local` here and in the containers |
| Docker isn't installed here, and installing it needs `sudo` | The Compose setup hasn't run on Docker yet. Its nginx config passed a local test on nginx 1.24 |
| `openapi-typescript` 7.13 needs TypeScript 5. npm's default is now TypeScript 7 | Pin TypeScript 5 (5.9.3 tested) |
| `--verdict` needs exactly Lean 4.34.0 (installed through elan). The first run compiles the kernel in about 24s and caches it in `~/.bend/bendtt/`, so later runs take about 1s | A fresh machine or CI needs elan with that toolchain, or `$BENDTT` set to a built kernel. Plain `bend PROOF.bend` needs neither |
| The termination checker rejected a self-call on the same schema in a different mode, and Bend won't infer `Equal.sym`'s arguments | Generators and proofs need some restructuring and explicit arguments. Expect this friction throughout |
| `Nat` runs as a 48-bit immediate with O(1) arithmetic, as fast as `U32` (100M mixed operations in 0.67s), and aborts past 2^48 instead of wrapping | Domain numbers are `Nat`, which needs no bit-level lemmas. Ids, minutes and days all fit |
| A universally quantified hypothesis is an affine closure, so a proof can use it once. Equality proofs are `Data` and reusable | Bag equality is stated over a concrete list (`agree`), not as a for-all |
| A literal fuel such as `improve(3n, ..)` inside a def makes the checker unroll it when comparing terms. It hangs with no message | Fuel and tuning reach solver defs as parameters |
| 10,000 appraisals, 1,000 contractors and 7 days plan in 18.3s on 1 thread and 5.3s on 12, within 44MB, on straight-line times | The 30-minute target looks reachable, before road lookups are added |
| Forking one search 2^2 ways gave 1.3x on 4,000 jobs, and 2^6 ways gave 2.9x, with no cost on one thread | Tasks never move, so unevenly loaded work needs far more tasks than cores. Measure fork depth instead of guessing |
| The proven checker built with `-o .mjs` ran under Node, accepting a good plan and rejecting a duplicated and a lost appraisal | The browser validator works through plain JS constructors |

Proof effort for the real rules is now measured. See the scorecard.

## Architecture

- **nginx:** the only public entry point. Terminates TLS, serves the built frontend, and proxies `/api/` to the web process.
- **Web process:** HTTP, API, auth, sessions, live updates. Stays responsive by never doing heavy work.
- **Solver process:** nightly planning and same-day repairs, parallel across cores.
- **Road process:** batch travel-time and geocoding lookups against on-disk data.
- **Pure core:** domain rules, plan validation, event replay and codecs, kept free of IO so `bend PROOF.bend` covers it. The checker also compiles to JS for the browser.
- **Storage:** append-only event log with snapshots, in Bend, with state rebuilt by replay.
- **Frontend:** a Preact single-page app in `frontend/`, talking to the backend only through the public API.

### Repository layout

```text
backend/    Bend code, LAWS.bend, PROOF.bend, Dockerfile
  web/      Web process
  core/     Pure core: types, lifecycle, plan checker, healing, planner
  proof/    Lemmas behind PROOF.bend
  test/     Concrete scenarios the laws don't cover
  solver/   Benchmark shell and synthetic instances, later the solver process
  road/     Road process (planned)
frontend/   TypeScript and Preact npm project
deploy/     nginx image and config
compose.yaml, compose.dev.yaml
```

`bend PROOF.bend` runs from `backend/`, and npm scripts run from `frontend/`. `openapi.json` lives in `backend/`, because the backend owns it.

### Local deployment

Compose runs the app the way a real deployment would, so nothing talks to the backend directly. Only nginx publishes ports, and every other service stays on the internal Docker network.

| Service | Role |
|---|---|
| `nginx` | TLS on port 8443, redirect from 8080, static frontend, proxy to the backend |
| `web` | Bend web process, built in a multi-stage image with Bend pinned by checksum |
| `solver`, `road` | Added in Milestones 2 and 3, with a shared data volume |
| `frontend` | Development only. Vite with hot reload behind nginx |

- **Real-world run:** `docker compose up --build` serves the built frontend, and is what Playwright, contract and load tests target.
- **Development:** `docker compose -f compose.yaml -f compose.dev.yaml watch` keeps the same nginx and TLS path, swaps in Vite, and rebuilds the backend on change.
- **Images:** the backend image fails to build if `bend PROOF.bend`, the Bend check or the scenarios fail. This hasn't run on Docker yet.
- **Certificates:** nginx creates a self-signed certificate in a Docker volume on first start. No key is ever committed.
- **Secrets:** later secrets come from a gitignored `.env` file, never from the images or Compose files.
- **Backend protection:** nginx buffers requests and limits body size, so slow or oversized clients never reach Bend's event loop. Server-Sent Events will need a route with buffering turned off.
- **Road data:** kept in a bind-mounted, gitignored `data/` folder on the Linux filesystem, because it's too large for an image.

### API contract

Every API route is a Bend value in one route table, holding its method, path, auth rule, request schema and response schemas. Everything else comes from that table:

1. **Handlers:** a handler's type is computed from its route, so a wrong response shape doesn't compile.
2. **Codecs:** JSON encoding and decoding are driven by the schema, with laws for conformance and round trips.
3. **Spec:** a Bend program walks the table and writes `openapi.json` (OpenAPI 3.1). The web process also serves it, so dealers can generate their own clients.
4. **Client:** `openapi-typescript` turns the spec into types, and the frontend calls the API through `openapi-fetch`.

```mermaid
flowchart LR
  T[Route table in Bend] --> H[Handlers and codecs]
  T --> G[Bend spec generator]
  G --> O[openapi.json]
  O --> C[Generated TypeScript types]
  C --> F[Preact frontend]
  F -->|HTTP| H
```

An API change is a Bend change. If the frontend's use of the API no longer matches, `tsc` fails.

`openapi.json` and the generated types are committed, and the check regenerates them and fails on any difference. A change to the API therefore always shows up in review.

The spike covered one POST route with strings, numbers, lists and objects. Still to build: path and query parameters, error responses, optional fields, enums, auth schemes, and named components, which the generated TypeScript needs for readable type names.

Live updates use Server-Sent Events, which `openapi-fetch` doesn't handle. Event payloads are still schemas in the route table, and a small typed wrapper around `EventSource` consumes them.

### Frontend project

- **Build:** Vite and Preact, on Node 24 LTS, with TypeScript pinned to 5 for `openapi-typescript`.
- **Type checking:** `strict`, plus `noUncheckedIndexedAccess` and `exactOptionalPropertyTypes`.
- **Linting:** `typescript-eslint` `strictTypeChecked` and `stylisticTypeChecked`, with zero warnings allowed and generated files excluded.
- **Formatting:** Prettier, enforced by the check.
- **Testing:** Vitest for units, and Playwright for each role's workflows, running through nginx.
- **Scripts:** `npm run check` runs type checking, linting, the format check, tests and the spec drift check. `npm run gen:api` regenerates the spec and client.
- **Development:** Vite runs behind nginx in Compose, so the browser always uses the same HTTPS origin as a real deployment.

The browser calls the proven checker through a Bend module built with `-o .mjs`. Its boundary is a single function taking and returning JSON strings, using the same proven codecs as the API. This avoids hand-mapping Bend's constructors in TypeScript. Its small declaration file is written by hand.

### Road data without holding it in RAM

1. Stream the `.pbf` once. Its blocks are compressed independently, so decompression can fan out across cores.
2. Keep only drivable roads, reducing nodes to junctions.
3. Split the network into geographic regions, stored as fixed-size records in files under 4GB.
4. Precompute shortcuts across each region's boundary so long trips don't load every region between them.
5. At solve time, load only regions near the stops and compute travel times only between pairs that could share a route.

Each contractor covers a limited area, so most lookups touch few regions.

### Solving in parallel

Contractor overlaps may chain into one giant national cluster, so we can't count on natural separation. The solver cuts the country into balanced regions, solves those in parallel, then shifts the boundaries and repeats so work can cross them. Balance matters because Bend's scheduler never moves a task once it's assigned.

## What the proofs cover

Proven so far in `LAWS.bend`, for the pure core:

- Every active appraisal is in exactly one place: a route, the backlog, or the exceptions queue.
- Every route starts and ends at the contractor's start point and visits no stop twice.
- Published routes respect hours, availability and deadlines, or the exception is recorded.
- Out-of-zip work is within the cap and flagged.
- After a cancellation, the appraisal is in no route.
- Healing never changes locked stops, and never makes a valid plan invalid.
- Parallel and sequential selection give the same answer.
- The optimizer never returns a worse score than its input.
- The planner only considers open routes, on or before the deadline, with the hours left, and only urgent work leaves its zips.

Healing is proven by construction: every edit rebuilds the route through `Route.remake`, so no runtime guard is involved, apart from the check that a reorder holds the same stops. The planner is the opposite. It isn't proven to build a valid plan. `publish` runs the proven checker on the result and falls back to the trivial plan, so what leaves is always valid, but a planner bug would show up as an empty plan instead of a failed proof.

Still to prove:

- Replaying a snapshot plus later events equals replaying the full log.
- Codecs round-trip.
- Every encoded API response conforms to its route's schema.
- Tenant isolation and role permissions hold for every request.
- Road paths exist in the graph, and their reported cost is correct.

Not proven:

- That routes are optimal. Quality is measured by benchmarks instead.
- That the planner places work at all. A valid plan may leave everything in the backlog, so `test/scenario.bend` covers this.
- That the planner handles the tightest deadline first. Also covered by the scenarios.
- That road times match reality. No law looks inside the travel time function, so swapping in real road times changes no proof.
- That the emitted `openapi.json` means the same thing as the Bend schema. Contract tests check real responses against the spec instead.
- The IO shell, process wiring and frontend. These rely on testing.

## Milestones

Sizes are relative. Each milestone ends with a passing `bend PROOF.bend`, and also `npm run check` once the frontend exists.

### 1. Core model and proof check (M)

Domain types, plan validity, the appraisal lifecycle, and the checker, with a small solver using straight-line distances.

**Done when:** the validity and healing laws are proven, and proof effort has been recorded.
**Go/no-go:** if these laws are too painful, reduce the proof scope before building further.
**Status:** done. All 40 laws pass `bend PROOF.bend`, and the result is go: the proof scope stays as planned. `bend PROOF.bend --verdict` also passes with the proven kernel, on Lean 4.34.0.

### 2. Road network (XL)

Gzip-style decompression and protobuf parsing in Bend, then the region pipeline above and batch travel-time queries. Start with one state, then the lower 48.

**Done when:** the full lower-48 build completes on this machine, within 15GB of RAM, and a sample of routes is within an agreed margin of a reference router.
**Go/no-go:** if the national build can't fit, revisit `.pbf` handling or graph detail.

### 3. National solver (L)

Synthetic data generator, nightly multi-day planning, contractor assignment, balance, and capped out-of-zip overflow.

**Done when:** a 10,000-appraisal, 1,000-contractor day solves in a proposed 30 minutes, no feasible deadline is missed, and results beat simple baselines. We'll also measure speedup on real solver work and benchmark against OR-Tools.

### 4. Web platform and API (XL)

HTTP/1.1, JSON, the route table and schema-driven codecs, the OpenAPI generator, event log and snapshots, password and API-key auth, the external API, organizations and roles, and process wiring. Also adds the generated client and contract tests to the existing frontend project, so the contract is proven end to end before the UI is built.

**Done when:** simulated dealer clients can create, read and cancel requests using the generated spec, real responses pass contract tests, a breaking API change fails `tsc`, data survives a crash, and tenant isolation is proven.

### 5. Geocoding (M)

Address lookup from OpenStreetMap and TIGER, including reading TIGER's zip archives, with zip assignment and a review queue for weak matches.

**Done when:** a sample of real addresses meets an agreed match rate, and weak matches are flagged instead of silently misplaced.

### 6. Same-day healing (L)

Cancellations, new requests, failed stops, sick contractors, live location, and backfill from neighbors or later days. Includes a simulator that plays out a full day.

**Done when:** a change produces updated routes within a proposed 5 seconds, locked stops never move, and the API stays responsive during repairs.

### 7. Frontend (L)

A TypeScript and Preact app using the generated API client. Admin view (national map, exceptions, overrides, contractors, metrics), requester view (submit, track, cancel, API keys), public booking and tracking pages, and a mobile-friendly contractor view. Includes live updates and instant drag validation by the proven checker.

**Done when:** each role can complete its full workflow in Playwright tests and in a browser, `npm run check` passes, and the design holds up in a real review.

### 8. Full-day demo and Bend scorecard (M)

A simulated national day from intake to the last completed appraisal, with 1,000 contractors, dealer API traffic, cancellations and live screens, all running through the Compose stack. Includes crash and load testing, then a written verdict on Bend.

**Done when:** the full day runs cleanly on this machine, and the scorecard is finished.

Milestones 5 and 7 can overlap with 4 once the first version of the spec exists.

## Bend scorecard

Tracked from Milestone 1 onward:

- Proof lines per line of code, and how far small rule changes ripple through proofs
- Bugs that proofs caught, and bugs that got past them
- Parallel speedup on real work, not synthetic loops
- Memory and throughput under realistic load
- Amount of infrastructure that had to be written from scratch
- How well Bend fits a normal frontend workflow, including API changes reaching TypeScript and any spec drift found by contract tests
- Developer friction, including compiler errors, missing features and `@unsafe` use

### Milestone 1 results

**Proof effort**

| Measure | Result |
|---|---|
| Laws | 40, in 369 lines |
| Core code | 1,833 lines |
| Proofs | 6,698 lines and 386 lemmas, or 3.7 proof lines per line of code |
| Checking everything | 0.5s |
| `@unsafe` or foreign code | None |
| `--verdict` | Passes on Lean 4.34.0, about 1s once the kernel is cached |

Proofs took most of the milestone's work, but they were steady. Once the design was right, most failures were one-line fixes to a proof script, and no law had to be weakened. The hard part was design: healing proofs are short because `Route.remake` makes every rebuilt route valid by construction. Without that, each of the six edits would have needed its own validity proof.

**How far changes ripple**

- Adding one field to the published audit touched 20 lines of core and 47 lines of proof, all in 3 equality lemmas. No healing proof changed.
- Moving the planner's constants into a `Tuning` record changed 2 lines of proof.

**Bugs**

Proofs caught no bug in the code as written. Every failed proof was a mistake in the proof script. The value showed up in two other places:

- **Design:** stating the cap law exposed that a whole-route cap can't survive a cancellation next to a locked stop. That changed the rule before any code existed.
- **Injected bugs:** we injected 25 bugs. `bend PROOF.bend` caught 22, and `test/scenario.bend` caught the other 3: all-zero drive times, the wrong deadline order, and a planner that drops every job.

Mutation testing also caught a bad law. `candidate_fits_route` said only that `Select.fits` passed, so a bug inside `fits` changed the law along with the code, and "planner ignores deadlines" got through. It became three laws stated in plain numbers. A law that restates the code proves nothing, so laws need checking too.

A failed proof doesn't always mean a false law. Some injected bugs were caught because a proof script stopped matching the code, and a harmless refactor would trip the same check.

**Parallel speedup on real work**

| Work | 1 thread | Best | Speedup |
|---|---|---|---|
| Plan check, 4,000 jobs | 24ms | 5ms on 12 threads | 4.8x |
| Assigning jobs, 10,000 jobs | 16.2s | 4.2s on 12 threads | 3.8x |
| Whole run, 10,000 jobs | 18.3s | 5.3s on 12 threads | 3.5x |
| Polishing routes, 10,000 jobs | 1,311ms | 465ms on 8 threads | 2.8x |

Output was identical at every thread count. This machine has 6 physical cores, so 12 threads flatters the thread count.

Two things decided these numbers:

- **Copying:** selecting through `take` and `drop` copied the route list for every job and gave no speedup. A balanced tree fixed that and nearly halved the single-thread time.
- **Fork depth:** we cut the search from 2^4 lanes to 2^2 on a hunch, and the 4-thread speedup fell from 2.3x to 1.3x. A sweep showed the opposite was true, with the best results around 2^6. A job's candidates cluster on a few routes and tasks never move, so over-splitting is the only way to balance them.

**Friction**

- **Rewriting:** `%e` replaces the right side of `e` with its left, which is easy to get backwards. It caused about ten failed attempts.
- **No inference or tactics:** every `Equal.trans` spells out each term, so proof lines run long. This is the main reason for the 3.7 ratio.
- **For-all hypotheses:** they can only be used once, which forced the `agree` workaround. This was the most surprising limit.
- **Silent hangs:** literal fuel in a def hangs the checker with no message or timeout. Finding it took bisecting the proof file law by law.
- **Missing lemmas:** Base has almost nothing on `Nat` order or addition, so `proof/logic.bend` holds about 900 lines of basics.
- **No work stealing:** a task stays where it starts, so load balance is on the programmer. Over-splitting works, but the right depth came from a sweep and may not hold for other work.
- **Match placement:** `match` can't follow a `let` or a rewrite on the same parameter, so lets move into each arm.
- **Eager evaluation:** `Bool.pick` evaluates both arms, and banned mutual recursion means thunks for lazy branches.
- **Good:** error messages show the expected and observed terms in context, and were nearly always enough. Checking is fast enough to run after every edit.

## Main risks

1. **Lower-48 road build:** decompression, parsing and region-building at this scale in Bend is the largest unknown, and 15GB of RAM is tight.
2. **Proof effort:** measured at 3.7 proof lines per line of code, and manageable. The risk now is the verbosity of proofs at web scale, not whether they can be done.
3. **Scale of road data in Bend's memory model:** lists and strings are expensive, so performance depends on staying in arrays.
4. **Geocoding quality:** free address data has gaps, particularly in rural areas.
5. **Phone GPS:** browsers allow geolocation only on trusted HTTPS or localhost. nginx provides HTTPS, but a phone won't trust the self-signed certificate, so a real-phone test needs a certificate the phone trusts. The fleet will use simulated locations.
6. **Local-only hosting:** no real outside dealer can reach the API, so the demo relies on simulated clients.
7. **Schema law at full scale:** the spike's law compared field names by length only, because Base has `String.eq` but no proof that it's reflexive. The real law needs that lemma, and proof effort on the full schema is unknown.
