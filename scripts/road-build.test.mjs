import assert from "node:assert/strict";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import test from "node:test";
import zlib from "node:zlib";
import { build, buildStates, ROAD_CLASSES } from "./road-build.mjs";

// A small protobuf encoder, just enough to write a .pbf by hand.
function varint(value) {
  const bytes = [];
  while (value >= 128) {
    bytes.push((value % 128) + 128);
    value = Math.floor(value / 128);
  }
  bytes.push(value);
  return Buffer.from(bytes);
}

const zigzag = (v) => (v < 0 ? -2 * v - 1 : 2 * v);
const key = (field, wire) => varint(field * 8 + wire);
const number = (field, value) => Buffer.concat([key(field, 0), varint(value)]);
const bytes = (field, value) => {
  const body = Buffer.from(value);
  return Buffer.concat([key(field, 2), varint(body.length), body]);
};
const packed = (field, values) =>
  bytes(field, Buffer.concat(values.map(varint)));

function deltas(values) {
  let last = 0;
  return values.map((value) => {
    const delta = value - last;
    last = value;
    return zigzag(delta);
  });
}

function block(type, payload) {
  const blob = Buffer.concat([
    number(2, payload.length),
    bytes(3, zlib.deflateSync(payload)),
  ]);
  const header = Buffer.concat([bytes(1, type), number(3, blob.length)]);
  const size = Buffer.alloc(4);
  size.writeUInt32BE(header.length);
  return Buffer.concat([size, header, blob]);
}

function dataBlock(strings, group) {
  const table = Buffer.concat(strings.map((s) => bytes(1, s)));
  return block("OSMData", Buffer.concat([bytes(1, table), bytes(2, group)]));
}

function nodesBlock(nodes) {
  const dense = Buffer.concat([
    packed(1, deltas(nodes.map((n) => n.id))),
    packed(8, deltas(nodes.map((n) => n.lat))),
    packed(9, deltas(nodes.map((n) => n.lon))),
  ]);
  return dataBlock([""], bytes(2, dense));
}

function waysBlock(ways) {
  const strings = [""];
  const index = (text) => {
    if (!strings.includes(text)) strings.push(text);
    return strings.indexOf(text);
  };
  const encoded = ways.map((way, i) => {
    const tags = Object.entries(way.tags);
    return bytes(
      3,
      Buffer.concat([
        number(1, i + 1),
        packed(
          2,
          tags.map(([k]) => index(k)),
        ),
        packed(
          3,
          tags.map(([, v]) => index(v)),
        ),
        packed(8, deltas(way.refs)),
      ]),
    );
  });
  return dataBlock(strings, Buffer.concat(encoded));
}

function words(file, width) {
  const raw = fs.readFileSync(file);
  const out = [];
  for (let i = 0; i < raw.length; i += width * 4) {
    const row = [];
    for (let j = 0; j < width; j++) row.push(raw.readUInt32LE(i + j * 4));
    out.push(row);
  }
  return out;
}

function run(blocks) {
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), "road-build-"));
  const pbf = path.join(dir, "map.osm.pbf");
  try {
    fs.writeFileSync(pbf, Buffer.concat(blocks));
    const result = build(pbf, dir);
    return {
      result,
      nodes: words(path.join(dir, "nodes.bin"), 2),
      edges: words(path.join(dir, "edges.bin"), 6),
      shapes: words(path.join(dir, "shapes.bin"), 2),
      leftovers: fs.readdirSync(dir).filter((name) => name.startsWith(".")),
    };
  } finally {
    fs.rmSync(dir, { recursive: true });
  }
}

// IDs past 32 bits, in two partitions, as in real OSM data.
const low = 2 ** 33;
const high = 2 ** 34;
const node = (id, north) => ({ id, lat: 340000000 + north, lon: -840000000 });
const nodes = [
  node(low + 1, 0),
  node(low + 2, 20000),
  node(low + 3, 30000),
  node(low + 6, 10000),
  node(high + 4, 40000),
  node(high + 5, 50000),
];
const a = low + 1;
const b = low + 2;
const c = low + 3;
const shapePoint = low + 6;
const d = high + 4;
const driveway = high + 5;

const map = () => [
  block("OSMHeader", Buffer.alloc(0)),
  nodesBlock(nodes),
  waysBlock([
    { tags: { highway: "residential" }, refs: [a, shapePoint, b, c] },
    {
      tags: { highway: "primary", oneway: "-1", maxspeed: "35 mph" },
      refs: [b, d],
    },
    { tags: { highway: "service" }, refs: [c, driveway] },
    { tags: { building: "yes" }, refs: [a, b] },
  ]),
];

test("cuts ways at junctions and renumbers nodes compactly", () => {
  const { result, nodes: out, edges } = run(map());
  assert.equal(result.nodes, 4);
  assert.equal(result.edges, 3);
  assert.equal(result.missing, 0);
  assert.deepEqual(
    out.map(([lat]) => lat),
    [340000000, 340020000, 340030000, 340040000],
  );
  assert.deepEqual(
    edges.map(([from, to]) => [from, to]),
    [
      [0, 1],
      [1, 2],
      [3, 1],
    ],
  );
});

test("keeps shape points out of the graph but in the shape file", () => {
  const { edges, shapes } = run(map());
  assert.equal(edges[0][5], 0);
  assert.equal(edges[1][5], 3);
  assert.deepEqual(
    shapes.slice(0, 3).map(([lat]) => lat),
    [340000000, 340010000, 340020000],
  );
});

test("stores a reversed one-way in travel order", () => {
  const { edges, shapes } = run(map());
  const [, , , , flags, shape] = edges[2];
  assert.equal(flags & 15, 4);
  assert.equal(ROAD_CLASSES[flags & 15][0], "primary");
  assert.equal(flags & 16, 16);
  assert.equal(shapes[shape][0], 340040000);
  assert.equal(shapes[shape + 1][0], 340020000);
  assert.equal(edges[0][4] & 16, 0);
});

test("computes meters and time from the road's speed", () => {
  const { edges } = run(map());
  // 0.002 degrees of latitude is about 222m. A residential road is 25 km/h.
  // 35 mph is 56 km/h, and traffic keeps cars to 80% of that, 45 km/h.
  assert.equal(edges[0][2], 222);
  assert.equal(edges[0][3], 320);
  assert.equal(edges[2][2], 222);
  assert.equal(edges[2][3], 178);
});

test("treats motorways and roundabouts as one-way unless told otherwise", () => {
  const { edges } = run([
    nodesBlock(nodes),
    waysBlock([
      { tags: { highway: "motorway" }, refs: [a, b] },
      { tags: { highway: "tertiary", junction: "roundabout" }, refs: [b, c] },
      { tags: { highway: "motorway", oneway: "no" }, refs: [c, d] },
    ]),
  ]);
  assert.deepEqual(
    edges.map((edge) => edge[4] & 16),
    [16, 16, 0],
  );
});

test("leaves out private roads unless cars are let back in", () => {
  const { edges } = run([
    nodesBlock(nodes),
    waysBlock([
      { tags: { highway: "residential", access: "private" }, refs: [a, b] },
      { tags: { highway: "residential", motor_vehicle: "no" }, refs: [b, c] },
      {
        tags: { highway: "residential", access: "private", motorcar: "yes" },
        refs: [c, d],
      },
      {
        tags: { highway: "residential", access: "yes", vehicle: "private" },
        refs: [d, driveway],
      },
    ]),
  ]);
  assert.equal(edges.length, 1);
});

test("drops an edge whose end has no node, and counts the gap", () => {
  const { result, edges } = run([
    nodesBlock(nodes.slice(0, 2)),
    waysBlock([{ tags: { highway: "residential" }, refs: [a, b, c] }]),
  ]);
  assert.equal(result.missing, 1);
  assert.equal(edges.length, 0);
});

test("removes its temporary files", () => {
  assert.deepEqual(run(map()).leftovers, []);
});

test("refuses nodes out of ID order", () => {
  assert.throws(
    () => run([nodesBlock([nodes[1], nodes[0]]), waysBlock([])]),
    /sorted/,
  );
});

// Four stops 0.5 degrees apart, about 55km, running north across a state line.
function statesRun(marginKm) {
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), "road-build-"));
  const stops = [
    { id: 10, lat: 340000000, lon: -840000000 },
    { id: 20, lat: 345000000, lon: -840000000 },
    { id: 30, lat: 350000000, lon: -840000000 },
    { id: 40, lat: 355000000, lon: -840000000 },
  ];
  const road = { highway: "primary" };
  const pbf = path.join(dir, "map.osm.pbf");
  const outlines = path.join(dir, "outlines");
  const box = (south, north) =>
    `name\n1\n -85 ${south}\n -83 ${south}\n -83 ${north}\n -85 ${north}\nEND\nEND\n`;
  try {
    fs.mkdirSync(outlines);
    fs.writeFileSync(path.join(outlines, "south.poly"), box(33.5, 34.7));
    fs.writeFileSync(path.join(outlines, "north.poly"), box(34.8, 36));
    fs.writeFileSync(path.join(outlines, "notes.txt"), "not an outline");
    fs.writeFileSync(
      pbf,
      Buffer.concat([
        nodesBlock(stops),
        waysBlock([
          { tags: road, refs: [10, 20] },
          { tags: road, refs: [20, 30] },
          { tags: road, refs: [30, 40] },
        ]),
      ]),
    );
    const result = buildStates(pbf, outlines, dir, marginKm);
    const read = (state) => ({
      nodes: words(path.join(dir, state, "nodes.bin"), 2),
      edges: words(path.join(dir, state, "edges.bin"), 6),
      shapes: words(path.join(dir, state, "shapes.bin"), 2),
    });
    return {
      result,
      south: read("south"),
      north: read("north"),
      folders: fs.readdirSync(dir).sort(),
    };
  } finally {
    fs.rmSync(dir, { recursive: true });
  }
}

test("gives each state its own numbering and shapes", () => {
  const { north } = statesRun(0);
  assert.deepEqual(
    north.nodes.map(([lat]) => lat),
    [350000000, 355000000],
  );
  assert.deepEqual(north.edges[0].slice(0, 2), [0, 1]);
  assert.equal(north.edges[0][5], 0);
  assert.deepEqual(
    north.shapes.map(([lat]) => lat),
    [350000000, 355000000],
  );
});

test("drops a road that crosses a border with no margin", () => {
  const { south, north } = statesRun(0);
  assert.equal(south.edges.length, 1);
  assert.equal(north.edges.length, 1);
});

test("keeps a border road in both states with a margin", () => {
  const { south, north } = statesRun(40);
  assert.equal(south.nodes.length, 3);
  assert.equal(north.nodes.length, 3);
  assert.equal(south.edges.length, 2);
  assert.equal(north.edges.length, 2);
  assert.deepEqual(
    north.shapes.slice(0, 2).map(([lat]) => lat),
    [345000000, 350000000],
  );
});

test("reports every state and leaves no national files behind", () => {
  const { result, folders } = statesRun(40);
  assert.deepEqual(Object.keys(result.states).sort(), ["north", "south"]);
  assert.equal(result.states.north.edges, 2);
  assert.equal(result.nodes, 4);
  assert.deepEqual(
    folders.filter((name) => name.startsWith(".")),
    [],
  );
});
