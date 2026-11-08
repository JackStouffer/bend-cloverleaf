// Runs the nightly pipeline on a synthetic instance, the way the solver
// process will get its inputs in production: one road process per state writes
// that state's travel-time matrix, then one solver process plans every state.
// Each run is its own process under a hard memory cap, because Bend's heap
// never shrinks and has no limit.
//
//   node scripts/nightly.mjs matrices <synth folder> <road data folder> <road binary> [limit] [depth]
//   node scripts/nightly.mjs solve <synth folder> <solver binary> <threads> [planner] [forks]
//
// matrices writes matrix.bin beside each state's points.bin, at the deepest
// lane depth up to `depth` that the road process accepts for that state, and
// records its timings in matrices.json. Set NIGHTLY_CAP=off where something
// else already caps memory, as Compose does.
import { spawnSync } from "node:child_process";
import fs from "node:fs";
import path from "node:path";

const UNREACHABLE = 4294967295;
const CAPS = { road: "1G", solver: "2G" };

export function allowedDepth(message) {
  const m = /the budget allows depth (\d+)/.exec(message);
  return m ? Number(m[1]) : null;
}

export function readMatrix(bytes) {
  const words = new Uint32Array(bytes.buffer, bytes.byteOffset, bytes.byteLength / 4);
  const count = words[0];
  if (words.length !== 1 + count * count) throw new Error(`a matrix of ${count} points needs ${1 + count * count} words, not ${words.length}`);
  let reached = 0;
  for (let i = 1; i < words.length; i++) if (words[i] !== UNREACHABLE) reached++;
  return { count, reached, at: (i, j) => (words[1 + i * count + j] === UNREACHABLE ? null : words[1 + i * count + j]) };
}

function capped(cap, bin, args) {
  if (process.env.NIGHTLY_CAP === "off") return [bin, args];
  return ["systemd-run", ["--user", "--scope", "-q", "-p", `MemoryMax=${cap}`, "-p", "MemorySwapMax=0", "timeout", "-s", "KILL", "3600", bin, ...args]];
}

function run(cap, bin, args) {
  const [cmd, all] = capped(cap, bin, args);
  const t0 = Date.now();
  const r = spawnSync(cmd, all, { encoding: "utf8", maxBuffer: 1 << 26 });
  return { status: r.status, out: (r.stdout ?? "") + (r.stderr ?? ""), ms: Date.now() - t0 };
}

function matrices(synthDir, roadDir, roadBin, limit = "36000", depth = "3") {
  const summary = JSON.parse(fs.readFileSync(path.join(synthDir, "summary.json"), "utf8"));
  const log = [];
  const t0 = Date.now();
  for (const s of summary.states) {
    const dir = path.join(synthDir, s.state);
    let d = Number(depth);
    for (;;) {
      const r = run(CAPS.road, roadBin, ["matrix", path.join(roadDir, s.state), path.join(dir, "points.bin"), path.join(dir, "matrix.bin"), limit, String(d)]);
      const fits = allowedDepth(r.out);
      if (r.status !== 0 && fits !== null && fits < d) {
        d = fits;
        continue;
      }
      if (r.status !== 0) throw new Error(`${s.state}: road exited ${r.status}\n${r.out}`);
      const m = readMatrix(fs.readFileSync(path.join(dir, "matrix.bin")));
      const points = s.crews + s.jobs;
      if (m.count !== points) throw new Error(`${s.state}: ${m.count} rows for ${points} points`);
      log.push({ state: s.state, points, depth: d, ms: r.ms, reached: m.reached });
      console.log(`${s.state}: ${points} points on ${2 ** d} lanes in ${(r.ms / 1000).toFixed(1)}s, ${((100 * m.reached) / (points * points)).toFixed(1)}% in reach`);
      break;
    }
  }
  const total = Date.now() - t0;
  fs.writeFileSync(path.join(synthDir, "matrices.json"), JSON.stringify({ limit: Number(limit), ms: total, states: log }, null, 2) + "\n");
  console.log(`all matrices in ${(total / 1000).toFixed(1)}s`);
}

// Each state's plan is written beside its inputs, as plan-<planner>.bin.
function solve(synthDir, solverBin, threads, planner = "planner", forks = "4") {
  const summary = JSON.parse(fs.readFileSync(path.join(synthDir, "summary.json"), "utf8"));
  const { limit } = JSON.parse(fs.readFileSync(path.join(synthDir, "matrices.json"), "utf8"));
  const states = summary.states.map((s) => s.state);
  const r = run(CAPS.solver, solverBin, ["+RTS", "--threads", threads, "-RTS", "national", synthDir, planner, String(limit), forks, ...states]);
  process.stdout.write(r.out);
  if (r.status !== 0) throw new Error(`solver exited ${r.status}`);
  console.log(`the solver process took ${(r.ms / 1000).toFixed(1)}s on ${threads} threads`);
}

const [command, ...args] = process.argv.slice(2);
if (import.meta.url === `file://${process.argv[1]}`) {
  if (command === "matrices" && args.length >= 3) matrices(...args);
  else if (command === "solve" && args.length >= 3) solve(...args);
  else {
    console.error("usage: node scripts/nightly.mjs matrices <synth folder> <road data folder> <road binary> [limit] [depth]\n       node scripts/nightly.mjs solve <synth folder> <solver binary> <threads> [planner] [forks]");
    process.exit(2);
  }
}
