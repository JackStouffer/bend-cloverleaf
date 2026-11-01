# Cloverleaf

Cloverleaf plans daily routes for about 1,000 auto appraisal contractors across the lower 48. It's also a proof of concept for whether Bend works for general-purpose web programming, so record friction honestly instead of working around it quietly.

[PLAN.md](PLAN.md) holds the requirements, architecture, milestones and proof scope. Read it before starting work, and keep it updated when a decision changes.

## Public code

The code here will be published publicly, so it must not include any secrets, envs or passwords. That covers commits, tests, fixtures, logs, docs and config examples.

## Bend rules

- Run `bend guide` to learn Bend before writing it. Also read `bend guide effects` before writing an effect, and `bend guide shaders` before writing parallel code.
- Use `LAWS.bend` to keep important rules.
- Run `bend PROOF.bend` before committing. It must print ALL PROOFS CHECK.
- Parallelize the code whenever possible.

## Commands

```bash
bend PROOF.bend                       # the proof gate
bend PROOF.bend --verdict             # recheck with the proven kernel
bend file.bend --check-only           # check without running
bend file.bend -o out                 # build a native binary
./out +RTS --threads 12 -RTS          # run on 12 CPU threads
bend page.html -o dist                # bundle a page that imports .bend files
bend base Map                         # look up a name in Base
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
- Prefer `Nat` fuel for long-running loops. Use `@unsafe` only when fuel won't work, and only in the IO shell.
- Everything is in Bend except the browser UI, which is plain JS calling non-IO Bend defs. Ask before adding an outside dependency or a C effect, because foreign code fails `--verdict`.
- Bend's JS target runs sequentially, so don't plan on parallel work in the browser.

## Data and performance

- Keep large data in `Array<U32>` (about 4 bytes per slot) or fixed-size records. Lists cost a cell per element and `String` about 24 bytes per character, so convert early.
- `File.size` fails above 4GB and `File.read_at` takes a `U32` offset. Keep runtime data files under 4GB. Sequential reads work past 4GB.
- Never load the whole road network into RAM. This machine has 15GB, and data should be streamed or loaded by region.
- `U32` is the widest integer in Base and it wraps silently. Check for overflow in totals and offsets, and remember that OSM node IDs need more than 32 bits.
- Parallel calls need balanced work, because tasks are never moved once assigned. Split by estimated cost, not by count.
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

## Benchmarks

- The compiler can collapse simple arithmetic loops, so use a workload it can't simplify, and distrust results that look too fast.
- When testing whether one request blocks another, confirm the slow job is still running when the second request arrives.
- Use a real load generator. Spawning `curl` in a loop measures `curl`.

## Scorecard

Keep the scorecard from PLAN.md current as work happens. Log missing features, confusing errors, `@unsafe` use, proof effort, and bugs that proofs caught or missed.
