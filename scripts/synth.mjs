// Realistic synthetic instances for the national solve, one per state. Runs
// before a benchmark, never in the app.
//
//   node scripts/synth.mjs <road folder> <outlines folder> <output folder> <crews> <jobs> <first day> [seed] [cap]
//
// Contractors and appraisals are shared out by 2020 census population, and
// every site and home is a real road junction inside the state's outline, so
// sites cluster where the roads do. A zip is a 0.1 degree cell of the state.
// Each cell goes to its nearest contractor, to any other nearly as near, and
// to every contractor whose home is within COVER_KM, so neighbouring
// contractors overlap. Hours, working days and deadlines vary, from a fixed
// seed so that runs compare like with like.
//
// Each state gets a folder with two files of little-endian U32 words:
//
//   instance.bin  1 (the format version), state FIPS, cap, first day, days,
//                 crew count, job count, then each crew:
//                   id, lat, lon, max minutes, day mask, zip count, zips...
//                 then each job: id, lat, lon, zip, due day, minutes
//   points.bin    every crew's home, then every job's site, as int32 lat, lon
//                 in degrees * 1e7, the road process's points format
//
// Bit k of a day mask means the contractor works day first + k. Coordinates in
// instance.bin are the core's: degrees * 1e4, longitude counted west. Ids rise
// through the states in order, so each state's are sorted.
import fs from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";

export const COVER_KM = 30;
const TIE = 1.25;
const CELL_SAMPLES = 20000;

// Census 2020 resident population. The names match the road data's folders.
export const STATES = [
  ["alabama", 1, 5024279], ["arizona", 4, 7151502], ["arkansas", 5, 3011524],
  ["california", 6, 39538223], ["colorado", 8, 5773714], ["connecticut", 9, 3605944],
  ["delaware", 10, 989948], ["district-of-columbia", 11, 689545], ["florida", 12, 21538187],
  ["georgia", 13, 10711908], ["idaho", 16, 1839106], ["illinois", 17, 12812508],
  ["indiana", 18, 6785528], ["iowa", 19, 3190369], ["kansas", 20, 2937880],
  ["kentucky", 21, 4505836], ["louisiana", 22, 4657757], ["maine", 23, 1362359],
  ["maryland", 24, 6177224], ["massachusetts", 25, 7029917], ["michigan", 26, 10077331],
  ["minnesota", 27, 5706494], ["mississippi", 28, 2961279], ["missouri", 29, 6154913],
  ["montana", 30, 1084225], ["nebraska", 31, 1961504], ["nevada", 32, 3104614],
  ["new-hampshire", 33, 1377529], ["new-jersey", 34, 9288994], ["new-mexico", 35, 2117522],
  ["new-york", 36, 20201249], ["north-carolina", 37, 10439388], ["north-dakota", 38, 779094],
  ["ohio", 39, 11799448], ["oklahoma", 40, 3959353], ["oregon", 41, 4237256],
  ["pennsylvania", 42, 13002700], ["rhode-island", 44, 1097379], ["south-carolina", 45, 5118425],
  ["south-dakota", 46, 886667], ["tennessee", 47, 6910840], ["texas", 48, 29145505],
  ["utah", 49, 3271616], ["vermont", 50, 643077], ["virginia", 51, 8631393],
  ["washington", 53, 7705281], ["west-virginia", 54, 1793716], ["wisconsin", 55, 5893718],
  ["wyoming", 56, 576851],
].map(([name, fips, population]) => ({ name, fips, population }));

// Shares in proportion to weight by largest remainder, then any share under the
// floor is raised to it, taking from the largest shares.
export function apportion(total, weights, floor) {
  if (total < floor * weights.length) throw new Error(`${total} is too few for ${weights.length} shares of ${floor}`);
  const sum = weights.reduce((a, b) => a + b, 0);
  const exact = weights.map((w) => (total * w) / sum);
  const shares = exact.map((x) => Math.floor(x));
  let left = total - shares.reduce((a, b) => a + b, 0);
  const order = exact.map((x, i) => [x - Math.floor(x), i]).sort((a, b) => b[0] - a[0] || a[1] - b[1]);
  for (const [, i] of order) {
    if (left === 0) break;
    shares[i]++;
    left--;
  }
  for (let i = 0; i < shares.length; i++) {
    while (shares[i] < floor) {
      const top = shares.indexOf(Math.max(...shares));
      shares[top]--;
      shares[i]++;
    }
  }
  return shares;
}

// Park and Miller's generator, as the Bend benchmark uses, scaled to [0, 1).
export function random(seed) {
  let x = seed % 2147483647 || 1;
  return () => {
    x = Number((BigInt(x) * 48271n) % 2147483647n);
    return (x - 1) / 2147483646;
  };
}

const pick = (rand, n) => Math.floor(rand() * n);

function weighted(rand, pairs) {
  let r = rand() * pairs.reduce((a, [w]) => a + w, 0);
  for (const [w, v] of pairs) {
    if ((r -= w) < 0) return v;
  }
  return pairs[pairs.length - 1][1];
}

// int32 degrees * 1e7 to the core's degrees * 1e4, longitude west.
export const toCore = (lat, lon) => ({ lat: Math.round(lat / 1000), lon: Math.round(-lon / 1000) });

export const zipOf = (fips, p) => fips * 10000000 + Math.floor(p.lat / 1000) * 2000 + Math.floor(p.lon / 1000);

function km(a, b) {
  const dlat = ((a.lat - b.lat) / 1e4) * 111.32;
  const dlon = ((a.lon - b.lon) / 1e4) * 111.32 * Math.cos(((a.lat + b.lat) / 2e4) * (Math.PI / 180));
  return Math.hypot(dlat, dlon);
}

// Each contractor's zips, sorted. cells[i] is a point in the cell with zip zips[i].
export function coverZips(homes, cells, zips, radiusKm) {
  const out = homes.map(() => []);
  cells.forEach((cell, i) => {
    const d = homes.map((h) => km(h, cell));
    const near = Math.min(...d);
    d.forEach((x, c) => {
      if (x <= near * TIE + 1e-9 || x <= radiusKm) out[c].push(zips[i]);
    });
  });
  return out.map((z) => [...new Set(z)].sort((a, b) => a - b));
}

// Most work Monday to Friday, with the first day a Monday. Some work Tuesday to
// Saturday, some six days, some any five, and some take a day off this week.
export function makeCrew(rand, id, home, first, span) {
  const shape = weighted(rand, [[65, "week"], [15, "late"], [5, "six"], [15, "any"]]);
  let offsets;
  if (shape === "week") offsets = [0, 1, 2, 3, 4];
  else if (shape === "late") offsets = [1, 2, 3, 4, 5];
  else if (shape === "six") offsets = [0, 1, 2, 3, 4, 5];
  else {
    const all = [0, 1, 2, 3, 4, 5, 6];
    while (all.length > 5) all.splice(pick(rand, all.length), 1);
    offsets = all;
  }
  if (rand() < 0.1) {
    const off = pick(rand, offsets.length);
    offsets = offsets.filter((_, i) => i !== off);
  }
  const days = offsets.filter((o) => o < span).map((o) => first + o);
  const maxMinutes = weighted(rand, [[10, 360], [15, 420], [55, 480], [15, 540], [5, 600]]);
  return { id, home, zips: [], maxMinutes, days };
}

// Deadlines lean early, and some can wait past the horizon.
export function makeJob(rand, id, site, zip, first, span) {
  const offset = weighted(rand, [
    [10, 0], [15, 1], [15, 2], [15, 3], [10, 4], [10, 5], [10, 6], [15, "later"],
  ]);
  const due = first + (offset === "later" ? span + pick(rand, 7) : offset);
  const minutes = weighted(rand, [[70, 20], [15, 15], [15, 30]]);
  return { id, site, zip, due, minutes };
}

export function encodeInstance(inst) {
  const w = [1, inst.state, inst.cap, inst.first, inst.days, inst.crews.length, inst.jobs.length];
  for (const c of inst.crews) {
    const mask = c.days.reduce((m, d) => m | (1 << (d - inst.first)), 0);
    w.push(c.id, c.home.lat, c.home.lon, c.maxMinutes, mask, c.zips.length, ...c.zips);
  }
  for (const j of inst.jobs) w.push(j.id, j.site.lat, j.site.lon, j.zip, j.due, j.minutes);
  return Uint32Array.from(w);
}

export function decodeInstance(words) {
  let i = 0;
  const next = () => words[i++];
  if (next() !== 1) throw new Error("unknown instance format");
  const inst = { state: next(), cap: next(), first: next(), days: next(), crews: [], jobs: [] };
  const crewCount = next();
  const jobCount = next();
  for (let c = 0; c < crewCount; c++) {
    const id = next();
    const home = { lat: next(), lon: next() };
    const maxMinutes = next();
    const mask = next();
    const days = Array.from({ length: inst.days }, (_, k) => inst.first + k).filter((_, k) => mask & (1 << k));
    const zips = Array.from({ length: next() }, next);
    inst.crews.push({ id, home, zips, maxMinutes, days });
  }
  for (let j = 0; j < jobCount; j++) {
    inst.jobs.push({ id: next(), site: { lat: next(), lon: next() }, zip: next(), due: next(), minutes: next() });
  }
  return inst;
}

// Osmosis .poly: a name, then rings of "lon lat" lines, each closed by END.
function readRings(file) {
  const rings = [];
  let ring = null;
  for (const line of fs.readFileSync(file, "utf8").split("\n").slice(1)) {
    const text = line.trim();
    if (text === "END") {
      if (ring !== null) rings.push(ring);
      ring = null;
    } else if (text !== "") {
      if (ring === null) ring = [];
      else ring.push(text.split(/\s+/).map(Number));
    }
  }
  return rings;
}

function inside(rings, lat, lon) {
  let hit = false;
  for (const ring of rings) {
    for (let i = 0, j = ring.length - 1; i < ring.length; j = i++) {
      const [xi, yi] = ring[i];
      const [xj, yj] = ring[j];
      if (yi > lat !== yj > lat && lon < ((xj - xi) * (lat - yi)) / (yj - yi) + xi) hit = !hit;
    }
  }
  return hit;
}

// Junctions inside the outline, drawn at random, as int32 pairs and core points.
function sampler(rand, nodes, rings) {
  const count = nodes.length / 2;
  return () => {
    for (let tries = 0; tries < 1000000; tries++) {
      const n = pick(rand, count);
      const lat = nodes[2 * n];
      const lon = nodes[2 * n + 1];
      if (inside(rings, lat / 1e7, lon / 1e7)) {
        const core = toCore(lat, lon);
        return { core, raw: [core.lat * 1000, -core.lon * 1000] };
      }
    }
    throw new Error("no junction inside the outline");
  };
}

function writeWords(file, words) {
  fs.writeFileSync(file, new Uint8Array(words.buffer, words.byteOffset, words.byteLength));
}

function main([roadDir, outlineDir, outDir, crewArg, jobArg, firstArg, seedArg = "1", capArg = "60"]) {
  if (!firstArg) {
    console.error("usage: node scripts/synth.mjs <road folder> <outlines folder> <output folder> <crews> <jobs> <first day> [seed] [cap]");
    process.exit(2);
  }
  const [crewTotal, jobTotal, first, seed, cap] = [crewArg, jobArg, firstArg, seedArg, capArg].map(Number);
  const span = 7;
  const weights = STATES.map((s) => s.population);
  const crewShares = apportion(crewTotal, weights, 1);
  const jobShares = apportion(jobTotal, weights, 1);
  const rand = random(seed);
  let crewId = 1;
  let jobId = 1;
  const summary = [];
  STATES.forEach((state, s) => {
    const raw = fs.readFileSync(path.join(roadDir, state.name, "nodes.bin"));
    const nodes = new Int32Array(raw.buffer, raw.byteOffset, raw.length / 4);
    const draw = sampler(rand, nodes, readRings(path.join(outlineDir, `${state.name}.poly`)));
    const cellOf = new Map();
    for (let i = 0; i < CELL_SAMPLES; i++) {
      const p = draw().core;
      const z = zipOf(state.fips, p);
      if (!cellOf.has(z)) cellOf.set(z, p);
    }
    const homes = Array.from({ length: crewShares[s] }, draw);
    const sites = Array.from({ length: jobShares[s] }, draw);
    for (const site of sites) {
      const z = zipOf(state.fips, site.core);
      if (!cellOf.has(z)) cellOf.set(z, site.core);
    }
    const zips = [...cellOf.keys()];
    const covered = coverZips(homes.map((h) => h.core), zips.map((z) => cellOf.get(z)), zips, COVER_KM);
    const crews = homes.map((h, i) => ({ ...makeCrew(rand, crewId++, h.core, first, span), zips: covered[i] }));
    const jobs = sites.map((site) => makeJob(rand, jobId++, site.core, zipOf(state.fips, site.core), first, span));
    const dir = path.join(outDir, state.name);
    fs.mkdirSync(dir, { recursive: true });
    writeWords(path.join(dir, "instance.bin"), encodeInstance({ state: state.fips, cap, first, days: span, crews, jobs }));
    writeWords(path.join(dir, "points.bin"), Int32Array.from([...homes, ...sites].flatMap((p) => p.raw)));
    summary.push({ state: state.name, fips: state.fips, crews: crews.length, jobs: jobs.length, zips: zips.length });
  });
  fs.writeFileSync(path.join(outDir, "summary.json"), JSON.stringify({ first, days: span, cap, seed, states: summary }, null, 2) + "\n");
  console.log(`${crewId - 1} contractors and ${jobId - 1} appraisals in ${summary.length} states`);
}

if (process.argv[1] === fileURLToPath(import.meta.url)) main(process.argv.slice(2));
