// Writes one state's road records as adjacency arrays, the form the road search
// spike reads. A two-way edge becomes two arcs.
//
//   node scripts/road-adjacency.mjs <state folder> <output file>
//
// Output is little-endian U32 words: the node count, the arc count, one first-arc
// index per node plus one past the end, then target and deciseconds per arc.
import fs from "node:fs";

const EDGE_WORDS = 6;
const ONE_WAY_FLAG = 1 << 4;

const [folder, output] = process.argv.slice(2);
if (!folder || !output) {
  console.error("usage: node scripts/road-adjacency.mjs <state folder> <file>");
  process.exit(1);
}

const raw = fs.readFileSync(`${folder}/edges.bin`);
const edges = new Uint32Array(raw.buffer, raw.byteOffset, raw.length / 4);
const nodes = fs.statSync(`${folder}/nodes.bin`).size / 8;

const first = new Uint32Array(nodes + 1);
for (let i = 0; i < edges.length; i += EDGE_WORDS) {
  first[edges[i] + 1]++;
  if (!(edges[i + 4] & ONE_WAY_FLAG)) first[edges[i + 1] + 1]++;
}
for (let i = 0; i < nodes; i++) first[i + 1] += first[i];

const arcs = first[nodes];
const next = first.slice();
const adjacency = new Uint32Array(arcs * 2);
const addArc = (from, to, deciseconds) => {
  adjacency[next[from] * 2] = to;
  adjacency[next[from]++ * 2 + 1] = deciseconds;
};
for (let i = 0; i < edges.length; i += EDGE_WORDS) {
  addArc(edges[i], edges[i + 1], edges[i + 3]);
  if (!(edges[i + 4] & ONE_WAY_FLAG)) {
    addArc(edges[i + 1], edges[i], edges[i + 3]);
  }
}

const words = new Uint32Array(3 + nodes + arcs * 2);
words[0] = nodes;
words[1] = arcs;
words.set(first, 2);
words.set(adjacency, 3 + nodes);
fs.writeFileSync(output, new Uint8Array(words.buffer));
console.log({ nodes, arcs, megabytes: words.byteLength / 1e6 });
