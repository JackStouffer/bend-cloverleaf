# Cloverleaf

Cloverleaf is a real-world test of [Bend](https://bend-lang.com), a new programming language that combines formal proofs with fast parallel execution. The goal is to find out how useful Bend is for general-purpose web programming by building a complete application with it, not a small demo.

**Status:** early. The pure core is done and proven: domain rules, a plan checker, same-day healing and a small planner on straight-line distances. It isn't wired to the web process yet, so the app itself is still a skeleton connecting a Bend service, a Preact page and nginx.

## Why this project exists

Bend promises that a compiler can check code against precise rules and run that code in parallel across every core. Those claims are easy to show on small benchmarks. It's much harder to show them on a working product with messy data, real users and everyday web plumbing.

Cloverleaf is meant to push on the places a real app would:

- **Proofs:** can business rules such as "no appraisal is on two routes" be proven at a reasonable cost, and do those proofs survive changing requirements?
- **Parallelism:** does real optimization work speed up across cores, or only synthetic loops?
- **Scale:** can Bend route across a national road network inside the 8GB of an ordinary server?
- **Everyday web work:** how painful is it to build HTTP, JSON, auth and storage, none of which Bend's base library includes?

The project will end with a written scorecard on Bend, covering what worked, what didn't, and what the proofs did and didn't catch. A failed experiment still counts as a useful result.

## What we're building

Cloverleaf is a route planner for a fictional auto appraisal company with about 1,000 contractors across the lower 48 states. Dealerships and individuals request appraisals, and each contractor drives a daily loop from their start point, usually home, through their appraisals and back.

This is the traveling salesman problem with a lot of real-world constraints:

- Each contractor covers a set of zip codes in one state, and those sets often overlap, so the planner also chooses who does each appraisal.
- Each appraisal takes about 20 minutes and has a deadline date.
- Contractors have daily hour limits and availability calendars.
- The system handles 5,000-10,000 appraisals per day.
- Cancellations and other same-day changes must heal routes that are already underway.

### Planned features

- Nightly national route planning, prioritizing deadlines and then balancing work across contractors
- Same-day route repair, including backfilling freed-up time
- An external API for dealers and other apps to submit and cancel requests
- Separate views for admins, requesters and contractors, with live updates
- Public booking and tracking pages for individuals
- Road routing and address lookup built from OpenStreetMap and US Census data, written in Bend, with a Node script preparing the raw data before deploy

The backend will be written entirely in Bend. The frontend will be a TypeScript and Preact app with strict type checking, strict ESLint and Prettier, just as a real team would set it up. Bend will generate the API's OpenAPI spec, and the frontend will call the API through a typed client generated from that spec. The company and all of the data are synthetic.

## Running it

Bend has no TLS, so the app runs behind nginx. Local development and testing use the same Docker Compose setup as a real deployment. You'll need Docker with the Compose and Buildx plugins.

For a real-world run with the built frontend:

```bash
docker compose up --build
```

For development with hot reload:

```bash
docker compose -f compose.yaml -f compose.dev.yaml watch
```

Then open https://localhost:8443. The certificate is self-signed, so your browser will warn you the first time.

## Repository layout

- `backend/`: Bend services and proofs. [LAWS.bend](backend/LAWS.bend) lists every rule the compiler has proven
- `frontend/`: TypeScript and Preact app
- `deploy/`: nginx image and config
- `compose.yaml`, `compose.dev.yaml`: local deployment

## Learn more

- [PLAN.md](PLAN.md): requirements, architecture, milestones, proof scope and risks
- [CLAUDE.md](CLAUDE.md): working rules for this repository
