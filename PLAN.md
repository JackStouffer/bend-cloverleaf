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
| Stack | Bend backend, with a plain JS UI calling proven Bend functions |
| Data | Realistic synthetic data |
| Hosting | Local machine only |
| Scope ends at | Appraisal marked complete. No report or photo workflow |

### Assumptions to correct if wrong

- Planning covers a rolling 7 days. The next day's routes are published after the nightly solve.
- Deadlines mean end of day in the appraisal's local time zone.
- Drive times come from road type and speed limits, with no live traffic.
- Stops that are completed or underway are locked during healing.
- Out-of-zip work is capped at 60 extra drive minutes by default, and admins can change this.
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
| Bend's JS target runs sequentially | Fine for the browser validator, but no solving in the browser |
| GPU build produced no `.gpu` file here (no CUDA, clang 18) | CPU only. GPU is out of scope |

Proof effort is still unmeasured. No laws have been written yet, so Milestone 1 tests that first.

## Architecture

- **Web process:** HTTP, API, auth, sessions, live updates. Stays responsive by never doing heavy work.
- **Solver process:** nightly planning and same-day repairs, parallel across cores.
- **Road process:** batch travel-time and geocoding lookups against on-disk data.
- **Pure core:** domain rules, plan validation, event replay and codecs, kept free of IO so `bend PROOF.bend` covers it. The checker also compiles to JS for the browser.
- **Storage:** append-only event log with snapshots, in Bend, with state rebuilt by replay.

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

Proven in `LAWS.bend`, for the pure core:

- Every active appraisal is in exactly one place: a route, the backlog, or the exceptions queue.
- Every route starts and ends at the contractor's start point and visits no stop twice.
- Published routes respect hours, availability and deadlines, or the exception is recorded.
- Out-of-zip work is within the cap and flagged.
- After a cancellation, the appraisal is in no route.
- Healing never changes locked stops, and never makes a valid plan invalid.
- Parallel and sequential selection give the same answer.
- The optimizer never returns a worse score than its input.
- Replaying a snapshot plus later events equals replaying the full log.
- Codecs round-trip.
- Tenant isolation and role permissions hold for every request.
- Road paths exist in the graph, and their reported cost is correct.

Not proven:

- That routes are optimal. Quality is measured by benchmarks instead.
- That road times match reality.
- The IO shell, process wiring and JS UI. These rely on testing.

## Milestones

Sizes are relative. Each milestone ends with a passing `bend PROOF.bend`.

### 1. Core model and proof check (M)

Domain types, plan validity, the appraisal lifecycle, and the checker, with a small solver using straight-line distances.

**Done when:** the validity and healing laws are proven, and proof effort has been recorded.
**Go/no-go:** if these laws are too painful, reduce the proof scope before building further.

### 2. Road network (XL)

Gzip-style decompression and protobuf parsing in Bend, then the region pipeline above and batch travel-time queries. Start with one state, then the lower 48.

**Done when:** the full lower-48 build completes on this machine, within 15GB of RAM, and a sample of routes is within an agreed margin of a reference router.
**Go/no-go:** if the national build can't fit, revisit `.pbf` handling or graph detail.

### 3. National solver (L)

Synthetic data generator, nightly multi-day planning, contractor assignment, balance, and capped out-of-zip overflow.

**Done when:** a 10,000-appraisal, 1,000-contractor day solves in a proposed 30 minutes, no feasible deadline is missed, and results beat simple baselines. We'll also measure speedup on real solver work and benchmark against OR-Tools.

### 4. Web platform and API (L)

HTTP/1.1, JSON, routing, event log and snapshots, password and API-key auth, the external API, organizations and roles, and process wiring.

**Done when:** simulated dealer clients can create, read and cancel requests, data survives a crash, and tenant isolation is proven.

### 5. Geocoding (M)

Address lookup from OpenStreetMap and TIGER, including reading TIGER's zip archives, with zip assignment and a review queue for weak matches.

**Done when:** a sample of real addresses meets an agreed match rate, and weak matches are flagged instead of silently misplaced.

### 6. Same-day healing (L)

Cancellations, new requests, failed stops, sick contractors, live location, and backfill from neighbors or later days. Includes a simulator that plays out a full day.

**Done when:** a change produces updated routes within a proposed 5 seconds, locked stops never move, and the API stays responsive during repairs.

### 7. Frontend (L)

Admin view (national map, exceptions, overrides, contractors, metrics), requester view (submit, track, cancel, API keys), public booking and tracking pages, and a mobile-friendly contractor view. Includes live updates and instant drag validation by the proven checker.

**Done when:** each role can complete its full workflow in a browser, and the design holds up in a real review.

### 8. Full-day demo and Bend scorecard (M)

A simulated national day from intake to the last completed appraisal, with 1,000 contractors, dealer API traffic, cancellations and live screens. Includes crash and load testing, then a written verdict on Bend.

**Done when:** the full day runs cleanly on this machine, and the scorecard is finished.

Milestones 4, 5 and 7 can overlap once their interfaces are agreed.

## Bend scorecard

Tracked from Milestone 1 onward:

- Proof lines per line of code, and how far small rule changes ripple through proofs
- Bugs that proofs caught, and bugs that got past them
- Parallel speedup on real work, not synthetic loops
- Memory and throughput under realistic load
- Amount of infrastructure that had to be written from scratch
- Developer friction, including compiler errors, missing features and `@unsafe` use

## Main risks

1. **Lower-48 road build:** decompression, parsing and region-building at this scale in Bend is the largest unknown, and 15GB of RAM is tight.
2. **Proof effort:** untested so far, and it could slow every later milestone.
3. **Scale of road data in Bend's memory model:** lists and strings are expensive, so performance depends on staying in arrays.
4. **Geocoding quality:** free address data has gaps, particularly in rural areas.
5. **Phone GPS:** browsers allow geolocation only on HTTPS or localhost, so a phone can't reach a plain local server. The fleet will use simulated locations, and a real-phone test needs a local TLS proxy.
6. **Local-only hosting:** no real outside dealer can reach the API, so the demo relies on simulated clients.
