// Checks the road build's output against its documented format, sharing no code
// with the build, so a bug there can't hide itself here. Exits non-zero if any
// state has a problem.
//
//   node scripts/check-road-data.mjs <output folder>
import fs from "node:fs";
import path from "node:path";

function load(file, Words) {
  const raw = fs.readFileSync(file);
  return new Words(raw.buffer, raw.byteOffset, raw.length / 4);
}

function check(folder) {
  const nodes = load(path.join(folder, "nodes.bin"), Int32Array);
  const edges = load(path.join(folder, "edges.bin"), Uint32Array);
  const shapes = load(path.join(folder, "shapes.bin"), Int32Array);
  const nodeCount = nodes.length / 2;
  const edgeCount = edges.length / 6;
  const pointCount = shapes.length / 2;
  const turns = load(path.join(folder, "turns.bin"), Uint32Array);
  const problems = { nodes: 0, references: 0, shapes: 0, ends: 0, turns: 0 };

  for (let i = 0; i < nodeCount; i++) {
    if (nodes[2 * i] === 0) problems.nodes++;
  }

  const sameAs = (point, node) =>
    shapes[2 * point] === nodes[2 * node] &&
    shapes[2 * point + 1] === nodes[2 * node + 1];

  for (let e = 0; e < edgeCount; e++) {
    const from = edges[6 * e];
    const to = edges[6 * e + 1];
    const shape = edges[6 * e + 5];
    const next = e + 1 < edgeCount ? edges[6 * e + 11] : pointCount;
    if (from >= nodeCount || to >= nodeCount) {
      problems.references++;
    } else if (next - shape < 2 || next > pointCount) {
      problems.shapes++;
    } else {
      if (!sameAs(shape, from)) problems.ends++;
      if (!sameAs(next - 1, to)) problems.ends++;
    }
  }
  // The turn graph numbers roads by direction first, then a depart and an
  // arrive node per junction, and links each junction's two directly.
  let directions = 0;
  for (let e = 0; e < edgeCount; e++) {
    directions += edges[6 * e + 4] & 16 ? 1 : 2;
  }
  const total = directions + 2 * nodeCount;
  let links = 0;
  for (let i = 0; i < turns.length; i += 3) {
    const from = turns[i];
    const to = turns[i + 1];
    if (from >= total || to >= total) problems.turns++;
    const depart = from >= directions && from < directions + nodeCount;
    if (depart && to === from + nodeCount) links++;
  }
  problems.turns += Math.abs(links - nodeCount);
  return { nodeCount, edgeCount, pointCount, problems };
}

const root = process.argv[2];
if (!root) {
  console.error("usage: node scripts/check-road-data.mjs <output folder>");
  process.exit(1);
}

let failed = 0;
const states = fs
  .readdirSync(root, { withFileTypes: true })
  .filter((entry) => entry.isDirectory() && !entry.name.startsWith("."))
  .map((entry) => entry.name)
  .sort();

for (const state of states) {
  const { nodeCount, edgeCount, pointCount, problems } = check(
    path.join(root, state),
  );
  const found = Object.entries(problems).filter(([, count]) => count > 0);
  if (found.length > 0) failed++;
  const note = found.map(([kind, count]) => `${count} bad ${kind}`).join(", ");
  console.log(
    `${state}: ${nodeCount} nodes, ${edgeCount} edges, ${pointCount} points${note && `, ${note}`}`,
  );
}

console.log(`${states.length} states checked, ${failed} with problems`);
if (failed > 0 || states.length === 0) process.exit(1);
