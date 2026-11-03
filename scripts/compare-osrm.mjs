// Compares the road process's drive times with OSRM's on the same OpenStreetMap
// data. This is Milestone 2's check against a reference router, and it shares no
// code with either side.
//
//   node scripts/compare-osrm.mjs sample <state folder> <state.poly> <count> <points file> [box]
//   node scripts/compare-osrm.mjs compare <points file> <matrix file> <limit> <OSRM URL>
//
// `sample` picks road junctions inside the state itself, not its margin, so both
// routers start each trip at the same point. A box, as west,south,east,north
// degrees, keeps them to part of a state, for an OSRM region too big to build whole. `compare` asks OSRM's table service
// about every pair the road process reached within the limit, in deciseconds. It
// passes if at least 90% of those trips are within 10% of OSRM's time.
import fs from "node:fs";

const UNREACHABLE = 4294967295;
const MARGIN = 0.1;
const PASS_SHARE = 0.9;
const ROWS_PER_REQUEST = 25;

function load(file, Words) {
  const raw = fs.readFileSync(file);
  return new Words(raw.buffer, raw.byteOffset, raw.length / 4);
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
      if (
        yi > lat !== yj > lat &&
        lon < ((xj - xi) * (lat - yi)) / (yj - yi) + xi
      ) {
        hit = !hit;
      }
    }
  }
  return hit;
}

function sample(folder, polyFile, count, output, box) {
  const [west, south, east, north] = box
    ? box.split(",").map(Number)
    : [-180, -90, 180, 90];
  const nodes = load(`${folder}/nodes.bin`, Int32Array);
  const rings = readRings(polyFile);
  const nodeCount = nodes.length / 2;
  let x = 12345;
  const next = (m) => {
    x = (Math.imul(x, 48271) >>> 0) % 2147483647;
    return x % m;
  };
  const points = new Int32Array(2 * count);
  for (let found = 0; found < count;) {
    const node = next(nodeCount);
    const lat = nodes[2 * node];
    const lon = nodes[2 * node + 1];
    const inBox =
      lat / 1e7 >= south &&
      lat / 1e7 <= north &&
      lon / 1e7 >= west &&
      lon / 1e7 <= east;
    if (!inBox || !inside(rings, lat / 1e7, lon / 1e7)) continue;
    points[2 * found] = lat;
    points[2 * found + 1] = lon;
    found++;
  }
  fs.writeFileSync(output, new Uint8Array(points.buffer));
}

async function osrmRows(url, points, from, to) {
  const count = points.length / 2;
  const coordinates = [];
  for (let i = 0; i < count; i++) {
    coordinates.push(`${points[2 * i + 1] / 1e7},${points[2 * i] / 1e7}`);
  }
  const sources = [];
  for (let i = from; i < to; i++) sources.push(i);
  const query = `${url}/table/v1/driving/${coordinates.join(";")}?sources=${sources.join(";")}&annotations=duration`;
  const response = await fetch(query);
  const body = await response.json();
  if (body.code !== "Ok") throw new Error(`OSRM: ${body.code} ${body.message}`);
  return body.durations;
}

const quantile = (sorted, q) => sorted[Math.floor(q * (sorted.length - 1))];

async function compare(pointsFile, matrixFile, limit, url) {
  const points = load(pointsFile, Int32Array);
  const matrix = load(matrixFile, Uint32Array);
  const count = points.length / 2;
  if (matrix[0] !== count) {
    throw new Error(`matrix holds ${matrix[0]} points, expected ${count}`);
  }
  const trips = [];
  let missed = 0;
  let unroutable = 0;
  for (let from = 0; from < count; from += ROWS_PER_REQUEST) {
    const to = Math.min(count, from + ROWS_PER_REQUEST);
    const rows = await osrmRows(url, points, from, to);
    for (let i = from; i < to; i++) {
      for (let j = 0; j < count; j++) {
        if (i === j) continue;
        const ours = matrix[1 + i * count + j];
        const theirs = rows[i - from][j];
        if (ours === UNREACHABLE) {
          if (theirs !== null && theirs * 10 <= 0.9 * limit) missed++;
          continue;
        }
        if (theirs === null) {
          unroutable++;
          continue;
        }
        trips.push({ i, j, ours: ours / 10, theirs });
      }
    }
  }
  const ratios = trips
    .filter((t) => t.theirs > 0)
    .map((t) => t.ours / t.theirs)
    .sort((a, b) => a - b);
  const within = trips.filter(
    (t) => Math.abs(t.ours - t.theirs) <= MARGIN * t.theirs,
  ).length;
  const buckets = [0, 5, 15, 30, 60, Infinity].map((minutes, k, all) => {
    if (k === all.length - 1) return null;
    const some = trips.filter(
      (t) => t.theirs >= minutes * 60 && t.theirs < all[k + 1] * 60,
    );
    const ok = some.filter(
      (t) => Math.abs(t.ours - t.theirs) <= MARGIN * t.theirs,
    ).length;
    const r = some.map((t) => t.ours / t.theirs).sort((a, b) => a - b);
    return {
      minutes: `${minutes}-${all[k + 1]}`,
      trips: some.length,
      within: some.length ? +(ok / some.length).toFixed(3) : null,
      medianRatio: r.length ? +quantile(r, 0.5).toFixed(3) : null,
    };
  });
  const worst = trips
    .map((t) => ({ ...t, gap: Math.abs(t.ours - t.theirs) / t.theirs }))
    .sort((a, b) => b.gap - a.gap)
    .slice(0, 8)
    .map(({ i, j, ours, theirs }) => ({
      from: [points[2 * i] / 1e7, points[2 * i + 1] / 1e7],
      to: [points[2 * j] / 1e7, points[2 * j + 1] / 1e7],
      oursMinutes: +(ours / 60).toFixed(1),
      osrmMinutes: +(theirs / 60).toFixed(1),
    }));
  const share = within / trips.length;
  const report = {
    trips: trips.length,
    within: +share.toFixed(3),
    pass: share >= PASS_SHARE,
    ratio: {
      p10: +quantile(ratios, 0.1).toFixed(3),
      median: +quantile(ratios, 0.5).toFixed(3),
      p90: +quantile(ratios, 0.9).toFixed(3),
    },
    missed,
    unroutable,
    buckets: buckets.filter((b) => b !== null),
    worst,
  };
  console.log(JSON.stringify(report, null, 2));
  if (!report.pass) process.exitCode = 1;
}

const [command, ...args] = process.argv.slice(2);
if (command === "sample" && (args.length === 4 || args.length === 5)) {
  sample(args[0], args[1], Number(args[2]), args[3], args[4]);
} else if (command === "compare" && args.length === 4) {
  await compare(args[0], args[1], Number(args[2]), args[3]);
} else {
  console.error(
    "usage: node scripts/compare-osrm.mjs sample <state folder> <state.poly> <count> <points file> [box]\n" +
      "       node scripts/compare-osrm.mjs compare <points file> <matrix file> <limit> <OSRM URL>",
  );
  process.exit(1);
}
