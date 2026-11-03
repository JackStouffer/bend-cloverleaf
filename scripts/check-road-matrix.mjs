// Checks a matrix from the Bend road process against a separate implementation,
// sharing no code with it: a brute-force nearest node and a plain Dijkstra over
// the same records. Exits non-zero if any cell differs.
//
//   node scripts/check-road-matrix.mjs sample <state folder> <count> <points file>
//   node scripts/check-road-matrix.mjs check <state folder> <points file> <matrix file> <limit>
//
// `sample` writes stops near random road nodes, as int32 degrees * 1e7. A limit is
// in deciseconds, and 4294967295 marks a stop out of reach.
import fs from "node:fs";

const EDGE_WORDS = 6;
const ONE_WAY_FLAG = 1 << 4;
const UNREACHABLE = 4294967295;
const JITTER = 100000;

function load(file, Words) {
  const raw = fs.readFileSync(file);
  return new Words(raw.buffer, raw.byteOffset, raw.length / 4);
}

function sample(folder, count, output) {
  const nodes = load(`${folder}/nodes.bin`, Int32Array);
  const nodeCount = nodes.length / 2;
  let x = 12345;
  const next = (m) => {
    x = (Math.imul(x, 48271) >>> 0) % 2147483647;
    return x % m;
  };
  const points = new Int32Array(2 * count);
  for (let i = 0; i < count; i++) {
    const node = next(nodeCount);
    points[2 * i] = nodes[2 * node] + next(JITTER) - JITTER / 2;
    points[2 * i + 1] = nodes[2 * node + 1] + next(JITTER) - JITTER / 2;
  }
  fs.writeFileSync(output, new Uint8Array(points.buffer));
}

function adjacency(folder, nodeCount) {
  const edges = load(`${folder}/edges.bin`, Uint32Array);
  const first = new Uint32Array(nodeCount + 1);
  for (let i = 0; i < edges.length; i += EDGE_WORDS) {
    first[edges[i] + 1]++;
    if (!(edges[i + 4] & ONE_WAY_FLAG)) first[edges[i + 1] + 1]++;
  }
  for (let i = 0; i < nodeCount; i++) first[i + 1] += first[i];
  const next = first.slice();
  const heads = new Uint32Array(first[nodeCount]);
  const costs = new Uint32Array(first[nodeCount]);
  const add = (from, to, cost) => {
    heads[next[from]] = to;
    costs[next[from]++] = cost;
  };
  for (let i = 0; i < edges.length; i += EDGE_WORDS) {
    add(edges[i], edges[i + 1], edges[i + 3]);
    if (!(edges[i + 4] & ONE_WAY_FLAG)) {
      add(edges[i + 1], edges[i], edges[i + 3]);
    }
  }
  return { first, heads, costs };
}

// The same metric as road/snap.bend: units of 1e-5 degrees, Bhaskara's cosine.
function nearest(nodes, lat, lon) {
  const degrees = Math.floor(lat / 1e7);
  const square = degrees * degrees;
  const cosine = Math.floor((1000 * (32400 - 4 * square)) / (32400 + square));
  let best = Infinity;
  let found = -1;
  for (let i = 0; i < nodes.length / 2; i++) {
    const north = Math.floor(Math.abs(nodes[2 * i] - lat) / 100);
    const east = Math.floor(Math.abs(nodes[2 * i + 1] - lon) / 100);
    const scaled = Math.floor((east * cosine) / 1000);
    const distance = north * north + scaled * scaled;
    if (distance < best) {
      best = distance;
      found = i;
    }
  }
  return found;
}

function search({ first, heads, costs }, source, limit, dist) {
  dist.fill(UNREACHABLE);
  dist[source] = 0;
  const keys = [0];
  const nodes = [source];
  const swap = (a, b) => {
    [keys[a], keys[b]] = [keys[b], keys[a]];
    [nodes[a], nodes[b]] = [nodes[b], nodes[a]];
  };
  while (keys.length > 0) {
    const key = keys[0];
    const node = nodes[0];
    swap(0, keys.length - 1);
    keys.pop();
    nodes.pop();
    for (let i = 0; ;) {
      let child = 2 * i + 1;
      if (child >= keys.length) break;
      if (child + 1 < keys.length && keys[child + 1] < keys[child]) child++;
      if (keys[child] >= keys[i]) break;
      swap(i, child);
      i = child;
    }
    if (key !== dist[node]) continue;
    for (let arc = first[node]; arc < first[node + 1]; arc++) {
      const reached = key + costs[arc];
      if (reached > limit || reached >= dist[heads[arc]]) continue;
      dist[heads[arc]] = reached;
      keys.push(reached);
      nodes.push(heads[arc]);
      for (let i = keys.length - 1; i > 0;) {
        const parent = (i - 1) >> 1;
        if (keys[parent] <= keys[i]) break;
        swap(i, parent);
        i = parent;
      }
    }
  }
}

function check(folder, pointsFile, matrixFile, limit) {
  const nodes = load(`${folder}/nodes.bin`, Int32Array);
  const points = load(pointsFile, Int32Array);
  const matrix = load(matrixFile, Uint32Array);
  const count = points.length / 2;
  if (matrix[0] !== count || matrix.length !== 1 + count * count) {
    throw new Error(`matrix holds ${matrix[0]} points, expected ${count}`);
  }
  const graph = adjacency(folder, nodes.length / 2);
  const stops = [];
  for (let i = 0; i < count; i++) {
    stops.push(nearest(nodes, points[2 * i], points[2 * i + 1]));
  }
  const dist = new Uint32Array(nodes.length / 2);
  let reached = 0;
  let wrong = 0;
  for (let i = 0; i < count; i++) {
    search(graph, stops[i], limit, dist);
    for (let j = 0; j < count; j++) {
      const got = matrix[1 + i * count + j];
      if (dist[stops[j]] !== UNREACHABLE) reached++;
      if (got !== dist[stops[j]]) {
        if (wrong++ < 5) {
          console.error(`${i} to ${j}: ${got}, expected ${dist[stops[j]]}`);
        }
      }
    }
  }
  console.log({ points: count, reached, wrong });
  if (wrong > 0) process.exit(1);
}

const [command, ...args] = process.argv.slice(2);
if (command === "sample" && args.length === 3) {
  sample(args[0], Number(args[1]), args[2]);
} else if (command === "check" && args.length === 4) {
  check(args[0], args[1], args[2], Number(args[3]));
} else {
  console.error(
    "usage: node scripts/check-road-matrix.mjs sample <state folder> <count> <points file>\n" +
      "       node scripts/check-road-matrix.mjs check <state folder> <points file> <matrix file> <limit>",
  );
  process.exit(1);
}
