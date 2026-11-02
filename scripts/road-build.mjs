// Turns an OpenStreetMap .pbf into fixed-size road records for the Bend road
// pipeline. Runs before deploy, with no dependencies beyond Node 24.
//
//   node scripts/road-build.mjs <file.osm.pbf> <outlines folder> <output folder>
//
// Nothing here sorts. Node IDs and way positions are direct addresses into
// fixed arrays, so memory doesn't grow with the size of the map.
//
// The outlines folder holds one Osmosis .poly file per state. Contractors never
// work across a state line, so each state gets its own folder, named after its
// .poly file, and the app only ever loads one state at a time. Roads don't stop
// at the border, so a state's graph runs MARGIN_KM past it. Without that, a
// drive between two in-state stops can be wrong or impossible.
//
// Output is little-endian U32 words, and every file stays under 4GB so that
// Bend can read it with File.read_at. Each state has three files, numbered on
// their own:
//
//   nodes.bin   2 words per junction: lat, lon, as int32 degrees * 1e7
//   edges.bin   6 words per edge: from, to, meters, deciseconds, flags, shape
//   shapes.bin  2 words per point: lat, lon, in travel order
//
// `from` and `to` are indexes into nodes.bin. `shape` is the index in
// shapes.bin of the edge's first point, and its last point is just before the
// next edge's `shape`. In `flags`, bits 0-3 are an index into ROAD_CLASSES and
// bit 4 means the edge is one-way, from `from` to `to`.
import fs from "node:fs";
import { fileURLToPath } from "node:url";
import zlib from "node:zlib";

// Service roads stay out of the routing graph. Speeds are km/h, used when a
// way has no usable maxspeed tag.
export const ROAD_CLASSES = [
  ["motorway", 105],
  ["motorway_link", 70],
  ["trunk", 90],
  ["trunk_link", 60],
  ["primary", 80],
  ["primary_link", 55],
  ["secondary", 70],
  ["secondary_link", 50],
  ["tertiary", 60],
  ["tertiary_link", 45],
  ["unclassified", 50],
  ["residential", 40],
  ["living_street", 15],
  ["road", 40],
];
const CLASS_INDEX = new Map(ROAD_CLASSES.map(([name], i) => [name, i]));

const ID_BITS = 24;
const ID_SPAN = 2 ** ID_BITS;
const ID_MASK = ID_SPAN - 1;
const BITMAP_WORDS = ID_SPAN / 32;
const POSITION_SPAN = 2 ** 22;
const LONGEST_WAY = 2 ** 16;
const MAX_WAYS = 2 ** 25;
const FLUSH_WORDS = 2 ** 14;
const OUTPUT_WORDS = 2 ** 18;
const MAX_FILE_BYTES = 2 ** 32 - 1;
const MAX_U32 = 2 ** 32 - 1;
const NONE = MAX_U32;
const EARTH_METERS = 6371008.8;
const ONE_WAY_FLAG = 1 << 4;
const GRID_DEGREES = 0.02;
const KM_PER_DEGREE = 111.2;
const EDGE_WORDS = 6;
const EDGE_CHUNK = 2 ** 16;

// How far a state's road graph runs past its border. Against a graph of the
// whole South, 20km left Georgia trips up to 26 minutes too slow, and 40km
// matched every pair.
export const MARGIN_KM = 40;

// Protobuf wire format. `at` is the shared read cursor.
let at = 0;

function varint(bytes) {
  let c = bytes[at++];
  if (c < 128) return c;
  let value = c & 127;
  for (let scale = 128; ; scale *= 128) {
    c = bytes[at++];
    value += (c & 127) * scale;
    if (c < 128) return value;
  }
}

function fields(bytes, start, end, visit) {
  at = start;
  while (at < end) {
    const key = varint(bytes);
    const wire = key & 7;
    if (wire === 0) {
      const value = varint(bytes);
      const next = at;
      visit(key >>> 3, value, 0, 0);
      at = next;
    } else if (wire === 2) {
      const length = varint(bytes);
      const from = at;
      visit(key >>> 3, 0, from, from + length);
      at = from + length;
    } else {
      at += wire === 1 ? 8 : 4;
    }
  }
}

function packed(bytes, start, end, out) {
  out.length = 0;
  at = start;
  while (at < end) out.push(varint(bytes));
  return out;
}

const zigzag = (v) => (v % 2 ? -(v + 1) / 2 : v / 2);

function readExactly(fd, buffer, position) {
  if (fs.readSync(fd, buffer, 0, buffer.length, position) !== buffer.length) {
    throw new Error("truncated .pbf file");
  }
}

function* dataBlocks(path) {
  const fd = fs.openSync(path, "r");
  const size = Buffer.alloc(4);
  for (let pos = 0; fs.readSync(fd, size, 0, 4, pos) === 4;) {
    const header = Buffer.alloc(size.readUInt32BE(0));
    readExactly(fd, header, pos + 4);
    let type = "";
    let dataLength = 0;
    fields(header, 0, header.length, (field, value, start, end) => {
      if (field === 1) type = header.latin1Slice(start, end);
      if (field === 3) dataLength = value;
    });
    const blob = Buffer.alloc(dataLength);
    readExactly(fd, blob, pos + 4 + header.length);
    pos += 4 + header.length + dataLength;
    if (type !== "OSMData") continue;
    let data = null;
    fields(blob, 0, dataLength, (field, _, start, end) => {
      if (field === 1) data = Buffer.from(blob.subarray(start, end));
      if (field === 3) data = zlib.inflateSync(blob.subarray(start, end));
    });
    if (data === null) throw new Error("unsupported .pbf compression");
    yield data;
  }
  fs.closeSync(fd);
}

function parseSpeed(text) {
  const match = /^(\d+(?:\.\d+)?)\s*(mph)?$/.exec(text);
  if (match === null) return 0;
  const speed = Number(match[1]) * (match[2] ? 1.609344 : 1);
  return Math.round(speed);
}

// Who may drive a road, from most to least specific, as in OSRM's car profile.
// The first of these a way has decides, so motorcar=yes reopens a private road.
const ACCESS_KEYS = ["motorcar", "motor_vehicle", "vehicle", "access"];
const CLOSED = new Set(["private", "no"]);

// Returns a way's class, speed and direction, or null if it isn't a road a
// contractor can drive. Private roads stay out like service roads, and a stop on
// one snaps to the nearest public road.
function roadTags(strings, keys, values) {
  let road;
  let speed = 0;
  let oneway;
  let roundabout = false;
  const access = new Array(ACCESS_KEYS.length);
  for (let i = 0; i < keys.length; i++) {
    const key = strings[keys[i]];
    const value = strings[values[i]];
    const rank = ACCESS_KEYS.indexOf(key);
    if (rank >= 0) access[rank] = value;
    else if (key === "highway") road = CLASS_INDEX.get(value);
    else if (key === "maxspeed") speed = parseSpeed(value);
    else if (key === "oneway") oneway = value;
    else if (key === "junction") {
      roundabout = value === "roundabout" || value === "circular";
    }
  }
  if (road === undefined) return null;
  const rule = access.find((value) => value !== undefined);
  if (rule !== undefined && CLOSED.has(rule)) return null;
  const motorway = road <= 1;
  let direction = 0;
  if (oneway === "-1" || oneway === "reverse") direction = -1;
  else if (oneway === "yes" || oneway === "true" || oneway === "1") {
    direction = 1;
  } else if (oneway !== "no" && (motorway || roundabout)) direction = 1;
  return { road, speed: speed || ROAD_CLASSES[road][1], direction };
}

function readWay(data, strings, start, end, keys, values, refs, onWay) {
  const from = [0, 0, 0];
  const to = [0, 0, 0];
  fields(data, start, end, (field, _, a, b) => {
    const i = field === 2 ? 0 : field === 3 ? 1 : field === 8 ? 2 : -1;
    if (i >= 0) {
      from[i] = a;
      to[i] = b;
    }
  });
  const tags = roadTags(
    strings,
    packed(data, from[0], to[0], keys),
    packed(data, from[1], to[1], values),
  );
  if (tags === null) return;
  packed(data, from[2], to[2], refs);
  let id = 0;
  for (let i = 0; i < refs.length; i++) {
    id += zigzag(refs[i]);
    refs[i] = id;
  }
  // A way tagged one-way against its drawn order is stored in travel order.
  if (tags.direction < 0) refs.reverse();
  onWay(refs, tags);
}

function readNodes(data, start, end, scale, onNode) {
  const from = [0, 0, 0];
  const to = [0, 0, 0];
  fields(data, start, end, (field, _, a, b) => {
    const i = field === 1 ? 0 : field === 8 ? 1 : field === 9 ? 2 : -1;
    if (i >= 0) {
      from[i] = a;
      to[i] = b;
    }
  });
  let [ids, lats, lons] = from;
  let id = 0;
  let lat = 0;
  let lon = 0;
  while (ids < to[0]) {
    at = ids;
    id += zigzag(varint(data));
    ids = at;
    at = lats;
    lat += zigzag(varint(data));
    lats = at;
    at = lons;
    lon += zigzag(varint(data));
    lons = at;
    onNode(
      id,
      Math.floor((scale.latOffset + lat * scale.granularity) / 100),
      Math.floor((scale.lonOffset + lon * scale.granularity) / 100),
    );
  }
}

function readBlock(data, onWay, onNode) {
  const strings = [];
  const groups = [];
  const scale = { granularity: 100, latOffset: 0, lonOffset: 0 };
  fields(data, 0, data.length, (field, value, start, end) => {
    if (field === 1) {
      fields(data, start, end, (_, __, a, b) => {
        strings.push(data.latin1Slice(a, b));
      });
    }
    if (field === 2) groups.push([start, end]);
    if (field === 17) scale.granularity = value;
    if (field === 19) scale.latOffset = zigzag(value);
    if (field === 20) scale.lonOffset = zigzag(value);
  });
  const keys = [];
  const values = [];
  const refs = [];
  for (const [start, end] of groups) {
    fields(data, start, end, (field, _, a, b) => {
      if (field === 3 && onWay) {
        readWay(data, strings, a, b, keys, values, refs, onWay);
      }
      if (field === 2 && onNode) readNodes(data, a, b, scale, onNode);
    });
  }
}

// Append-only partition files, with one small fixed buffer per partition.
class PartitionSink {
  buffers = new Map();

  constructor(folder, width) {
    this.folder = folder;
    this.width = width;
    fs.mkdirSync(folder, { recursive: true });
  }

  buffer(partition) {
    let entry = this.buffers.get(partition);
    if (entry === undefined) {
      entry = { words: new Uint32Array(FLUSH_WORDS), used: 0 };
      this.buffers.set(partition, entry);
    }
    if (entry.used + this.width > FLUSH_WORDS) this.flush(partition, entry);
    return entry;
  }

  flush(partition, entry) {
    if (entry.used === 0) return;
    fs.appendFileSync(
      `${this.folder}/${partition}`,
      new Uint8Array(entry.words.buffer, 0, entry.used * 4),
    );
    entry.used = 0;
  }

  close() {
    for (const [partition, entry] of this.buffers) {
      this.flush(partition, entry);
    }
    this.buffers.clear();
  }
}

// One finished output file, with a check that Bend will be able to read it.
class OutputFile {
  words = new Uint32Array(OUTPUT_WORDS);
  used = 0;
  bytes = 0;

  constructor(path) {
    this.fd = fs.openSync(path, "w");
  }

  put(...values) {
    if (this.used + values.length > OUTPUT_WORDS) this.flush();
    for (const value of values) this.words[this.used++] = value;
  }

  // Writes a run of words already in file format, past the buffer.
  putBytes(bytes) {
    this.flush();
    fs.writeSync(this.fd, bytes);
    this.grow(bytes.length);
  }

  flush() {
    fs.writeSync(this.fd, new Uint8Array(this.words.buffer, 0, this.used * 4));
    this.grow(this.used * 4);
    this.used = 0;
  }

  grow(bytes) {
    this.bytes += bytes;
    if (this.bytes > MAX_FILE_BYTES) {
      throw new Error("output file reached 4GB, which Bend can't address");
    }
  }

  close() {
    this.flush();
    fs.closeSync(this.fd);
  }
}

function loadWords(path, into) {
  const fd = fs.openSync(path, "r");
  const bytes = fs.fstatSync(fd).size;
  if (bytes > into.byteLength) throw new Error(`${path} outgrew its buffer`);
  fs.readSync(fd, new Uint8Array(into.buffer, 0, bytes), 0, bytes, 0);
  fs.closeSync(fd);
  return bytes / 4;
}

function popcount(v) {
  v -= (v >>> 1) & 0x55555555;
  v = (v & 0x33333333) + ((v >>> 2) & 0x33333333);
  return (((v + (v >>> 4)) & 0x0f0f0f0f) * 0x01010101) >>> 24;
}

function fillRanks(bits, ranks) {
  let total = 0;
  for (let i = 0; i < BITMAP_WORDS; i++) {
    ranks[i] = total;
    total += popcount(bits[i]);
  }
  ranks[BITMAP_WORDS] = total;
}

const hasBit = (bits, x) => (bits[x >>> 5] >>> (x & 31)) & 1;
const setBit = (bits, x) => {
  bits[x >>> 5] |= 1 << (x & 31);
};
const rankOf = (bits, ranks, x) =>
  ranks[x >>> 5] + popcount(bits[x >>> 5] & ((2 ** (x & 31) - 1) >>> 0));

function positionPartition(starts, position) {
  let lo = 0;
  let hi = starts.length - 1;
  while (lo < hi) {
    const mid = (lo + hi + 1) >> 1;
    if (starts[mid] <= position) lo = mid;
    else hi = mid - 1;
  }
  return lo;
}

// Pass 1: every road reference goes to a file for its node ID's partition. A
// partition number plus 24 bits covers any OSM ID, and the position of a
// reference is all that's needed to put it back in order later.
function waysPass(pbfPath, temp) {
  const refs = new PartitionSink(`${temp}/refs`, 2);
  const ways = new Uint32Array(MAX_WAYS * 2);
  const starts = [0];
  let wayCount = 0;
  let position = 0;
  for (const data of dataBlocks(pbfPath)) {
    readBlock(
      data,
      (way, tags) => {
        if (wayCount === MAX_WAYS) throw new Error("too many ways");
        if (position + way.length > MAX_U32) throw new Error("U32 overflow");
        if (way.length > LONGEST_WAY) throw new Error("way too long");
        if (position - starts[starts.length - 1] >= POSITION_SPAN) {
          starts.push(position);
        }
        const oneWay = tags.direction === 0 ? 0 : ONE_WAY_FLAG;
        ways[wayCount * 2] = position;
        ways[wayCount * 2 + 1] = tags.road | oneWay | (tags.speed << 5);
        wayCount++;
        for (let i = 0; i < way.length; i++) {
          const partition = Math.floor(way[i] / ID_SPAN);
          const entry = refs.buffer(partition);
          const end = i === 0 || i === way.length - 1 ? 1 : 0;
          const low = way[i] - partition * ID_SPAN;
          entry.words[entry.used++] = (low | (end << ID_BITS)) >>> 0;
          entry.words[entry.used++] = position++;
        }
      },
      null,
    );
  }
  refs.close();
  return { ways, wayCount, starts, position };
}

// Pass 2: the file is sorted by ID, so nodes arrive in partition order and only
// one partition is ever active. Each junction's number is its partition's base
// plus its rank, which replaces OSM IDs with compact U32s.
function nodesPass(pbfPath, temp, nodesFile, starts) {
  const coords = new PartitionSink(`${temp}/coords`, 4);
  const partitions = fs
    .readdirSync(`${temp}/refs`)
    .map(Number)
    .sort((a, b) => a - b);
  const seen = new Uint32Array(BITMAP_WORDS);
  const junction = new Uint32Array(BITMAP_WORDS);
  const seenRanks = new Uint32Array(BITMAP_WORDS + 1);
  const junctionRanks = new Uint32Array(BITMAP_WORDS + 1);
  const places = new Int32Array(ID_SPAN * 2);
  const records = new Uint32Array(ID_SPAN * 8);
  let junctions = 0;
  let missing = 0;
  let lastId = -1;
  let next = 0;
  let current = -1;

  const open = (partition) => {
    seen.fill(0);
    junction.fill(0);
    const count = loadWords(`${temp}/refs/${partition}`, records);
    for (let i = 0; i < count; i += 2) {
      const x = records[i] & ID_MASK;
      if (records[i] >>> ID_BITS || hasBit(seen, x)) setBit(junction, x);
      setBit(seen, x);
    }
    fillRanks(seen, seenRanks);
    fillRanks(junction, junctionRanks);
    places.fill(0, 0, seenRanks[BITMAP_WORDS] * 2);
    current = partition;
  };

  const finish = () => {
    for (let word = 0; word < BITMAP_WORDS; word++) {
      for (let bits = junction[word]; bits !== 0; bits &= bits - 1) {
        const x = word * 32 + (31 - Math.clz32(bits & -bits));
        const slot = rankOf(seen, seenRanks, x) * 2;
        nodesFile.put(places[slot], places[slot + 1]);
      }
    }
    const count = loadWords(`${temp}/refs/${current}`, records);
    for (let i = 0; i < count; i += 2) {
      const x = records[i] & ID_MASK;
      const slot = rankOf(seen, seenRanks, x) * 2;
      if (places[slot] === 0) missing++;
      const entry = coords.buffer(positionPartition(starts, records[i + 1]));
      entry.words[entry.used++] = records[i + 1];
      entry.words[entry.used++] = places[slot];
      entry.words[entry.used++] = places[slot + 1];
      entry.words[entry.used++] = hasBit(junction, x)
        ? junctions + rankOf(junction, junctionRanks, x)
        : NONE;
    }
    junctions += junctionRanks[BITMAP_WORDS];
    fs.rmSync(`${temp}/refs/${current}`);
    current = -1;
    next++;
  };

  const advance = (partition) => {
    while (next < partitions.length && partitions[next] < partition) {
      if (current !== partitions[next]) open(partitions[next]);
      finish();
    }
    if (partitions[next] === partition && current !== partition) {
      open(partition);
    }
  };

  for (const data of dataBlocks(pbfPath)) {
    let nodes = 0;
    readBlock(data, null, (id, lat, lon) => {
      nodes++;
      if (id <= lastId) throw new Error(".pbf nodes aren't sorted by ID");
      lastId = id;
      const partition = Math.floor(id / ID_SPAN);
      if (partition !== current) advance(partition);
      if (partition !== current) return;
      const x = id - partition * ID_SPAN;
      if (!hasBit(seen, x)) return;
      const slot = rankOf(seen, seenRanks, x) * 2;
      places[slot] = lat;
      places[slot + 1] = lon;
    });
    if (nodes === 0) break; // Sorted by type, so no more nodes can follow.
  }
  advance(Infinity);
  coords.close();
  return { junctions, missing };
}

function haversine(lat1, lon1, lat2, lon2) {
  const toRadians = Math.PI / 180 / 1e7;
  const a = lat1 * toRadians;
  const b = lat2 * toRadians;
  const dLat = b - a;
  const dLon = (lon2 - lon1) * toRadians;
  const h =
    Math.sin(dLat / 2) ** 2 +
    Math.cos(a) * Math.cos(b) * Math.sin(dLon / 2) ** 2;
  return 2 * EARTH_METERS * Math.asin(Math.sqrt(h));
}

// Pass 3: a position is a direct index, so each partition loads with no sort.
// Partitions start at a way boundary, so no way crosses two of them.
function edgesPass(temp, first, edgesFile, shapesFile) {
  const { ways, wayCount, starts, position } = first;
  const size = POSITION_SPAN + LONGEST_WAY;
  const records = new Uint32Array(size * 4);
  const lats = new Int32Array(size);
  const lons = new Int32Array(size);
  const numbers = new Uint32Array(size);
  let edges = 0;
  let points = 0;
  let way = 0;

  const emit = (from, to, tags) => {
    if (lats[from] === 0 || lats[to] === 0) return;
    const shape = points;
    let meters = 0;
    let previous = from;
    shapesFile.put(lats[from], lons[from]);
    points++;
    for (let i = from + 1; i <= to; i++) {
      if (lats[i] === 0) continue;
      meters += haversine(lats[previous], lons[previous], lats[i], lons[i]);
      shapesFile.put(lats[i], lons[i]);
      points++;
      previous = i;
    }
    const speed = tags >>> 5;
    edgesFile.put(
      numbers[from],
      numbers[to],
      Math.max(1, Math.round(meters)),
      Math.max(1, Math.round((meters / speed) * 36)),
      tags & 31,
      shape,
    );
    edges++;
  };

  for (let q = 0; q < starts.length; q++) {
    const count = loadWords(`${temp}/coords/${q}`, records);
    const base = starts[q];
    for (let i = 0; i < count; i += 4) {
      const slot = records[i] - base;
      lats[slot] = records[i + 1];
      lons[slot] = records[i + 2];
      numbers[slot] = records[i + 3];
    }
    const end = q + 1 < starts.length ? starts[q + 1] : position;
    for (; way < wayCount && ways[way * 2] < end; way++) {
      const stop = way + 1 < wayCount ? ways[way * 2 + 2] : position;
      let from = ways[way * 2] - base;
      for (let i = from + 1; i < stop - base; i++) {
        if (numbers[i] === NONE) continue;
        emit(from, i, ways[way * 2 + 1]);
        from = i;
      }
    }
    fs.rmSync(`${temp}/coords/${q}`);
  }
  return { edges, points };
}

export function build(pbfPath, outDir) {
  const temp = `${outDir}/.road-build-temp`;
  fs.rmSync(temp, { recursive: true, force: true });
  fs.mkdirSync(temp, { recursive: true });
  const nodesFile = new OutputFile(`${outDir}/nodes.bin`);
  const edgesFile = new OutputFile(`${outDir}/edges.bin`);
  const shapesFile = new OutputFile(`${outDir}/shapes.bin`);

  const first = waysPass(pbfPath, temp);
  const second = nodesPass(pbfPath, temp, nodesFile, first.starts);
  const third = edgesPass(temp, first, edgesFile, shapesFile);

  nodesFile.close();
  edgesFile.close();
  shapesFile.close();
  fs.rmSync(temp, { recursive: true, force: true });
  return {
    ways: first.wayCount,
    refs: first.position,
    nodes: second.junctions,
    edges: third.edges,
    points: third.points,
    missing: second.missing,
  };
}

// A .poly file is a name, then rings of "lon lat" lines, each closed by END,
// then a last END. Holes are marked but need no special case, because counting
// edge crossings already treats them as outside.
function readRings(path) {
  const rings = [];
  let ring = null;
  for (const line of fs.readFileSync(path, "utf8").split("\n").slice(1)) {
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

// A grid over one state and its margin, holding each cell's distance from the
// state in km. Looking a node up is one array read.
class StateGrid {
  constructor(rings, marginKm) {
    const points = rings.flat();
    const lats = points.map(([, lat]) => lat);
    const lons = points.map(([lon]) => lon);
    const pad = marginKm / KM_PER_DEGREE / 0.6 + GRID_DEGREES;
    this.south = Math.min(...lats) - pad;
    this.west = Math.min(...lons) - pad;
    this.rows = Math.ceil(
      (Math.max(...lats) + pad - this.south) / GRID_DEGREES,
    );
    this.columns = Math.ceil(
      (Math.max(...lons) + pad - this.west) / GRID_DEGREES,
    );
    this.margin = marginKm;
    this.distance = new Float32Array(this.rows * this.columns).fill(Infinity);
    this.fill(rings);
    const middle = (Math.min(...lats) + Math.max(...lats)) / 2;
    this.spread(
      GRID_DEGREES * KM_PER_DEGREE,
      GRID_DEGREES * KM_PER_DEGREE * Math.cos((middle * Math.PI) / 180),
    );
  }

  // Scanline fill: each row flips between outside and inside at each crossing.
  fill(rings) {
    for (let row = 0; row < this.rows; row++) {
      const lat = this.south + (row + 0.5) * GRID_DEGREES;
      const crossings = [];
      for (const ring of rings) {
        for (let i = 0, j = ring.length - 1; i < ring.length; j = i++) {
          const [lonA, latA] = ring[i];
          const [lonB, latB] = ring[j];
          if (latA > lat !== latB > lat) {
            crossings.push(
              lonA + ((lat - latA) / (latB - latA)) * (lonB - lonA),
            );
          }
        }
      }
      crossings.sort((a, b) => a - b);
      for (let i = 0; i + 1 < crossings.length; i += 2) {
        const from = Math.ceil((crossings[i] - this.west) / GRID_DEGREES - 0.5);
        const to = (crossings[i + 1] - this.west) / GRID_DEGREES - 0.5;
        for (let column = from; column <= to; column++) {
          this.distance[row * this.columns + column] = 0;
        }
      }
    }
  }

  // Two sweeps of a chamfer distance transform.
  spread(rowKm, columnKm) {
    const { distance, rows, columns } = this;
    const diagonalKm = Math.hypot(rowKm, columnKm);
    const near = [
      [-1, -1, diagonalKm],
      [-1, 0, rowKm],
      [-1, 1, diagonalKm],
      [0, -1, columnKm],
    ];
    const sweep = (direction) => {
      const first = direction > 0 ? 0 : rows * columns - 1;
      for (let i = first; i >= 0 && i < rows * columns; i += direction) {
        const row = Math.floor(i / columns);
        const column = i - row * columns;
        for (const [dRow, dColumn, km] of near) {
          const y = row + dRow * direction;
          const x = column + dColumn * direction;
          if (y < 0 || y >= rows || x < 0 || x >= columns) continue;
          const reach = distance[y * columns + x] + km;
          if (reach < distance[i]) distance[i] = reach;
        }
      }
    };
    sweep(1);
    sweep(-1);
  }

  covers(lat, lon) {
    const row = Math.floor((lat / 1e7 - this.south) / GRID_DEGREES);
    const column = Math.floor((lon / 1e7 - this.west) / GRID_DEGREES);
    if (row < 0 || row >= this.rows || column < 0 || column >= this.columns) {
      return false;
    }
    return this.distance[row * this.columns + column] <= this.margin;
  }
}

function loadInts(path) {
  const bytes = fs.statSync(path).size;
  const words = new Int32Array(bytes / 4);
  const fd = fs.openSync(path, "r");
  if (bytes > 0) fs.readSync(fd, new Uint8Array(words.buffer), 0, bytes, 0);
  fs.closeSync(fd);
  return words;
}

// Yields edges a chunk at a time, each chunk ending with one extra record so
// that an edge can see where the next edge's shape starts.
function* edgeChunks(fd, total) {
  const words = new Uint32Array((EDGE_CHUNK + 1) * EDGE_WORDS);
  const view = new Uint8Array(words.buffer);
  for (let first = 0; first < total; first += EDGE_CHUNK) {
    const count = Math.min(EDGE_CHUNK, total - first);
    const extra = first + count < total ? 1 : 0;
    const bytes = (count + extra) * EDGE_WORDS * 4;
    fs.readSync(fd, view, 0, bytes, first * EDGE_WORDS * 4);
    yield { words, count, last: extra === 0 };
  }
}

function splitState(national, stateDir, grid, local) {
  const { nodes, nodesPath, edgesPath, shapesPath } = national;
  fs.mkdirSync(stateDir, { recursive: true });
  const nodesFile = new OutputFile(`${stateDir}/nodes.bin`);
  const edgesFile = new OutputFile(`${stateDir}/edges.bin`);
  const shapesFile = new OutputFile(`${stateDir}/shapes.bin`);
  let nodeCount = 0;
  for (let i = 0; i < nodes.length; i += 2) {
    const keep = grid.covers(nodes[i], nodes[i + 1]);
    local[i / 2] = keep ? nodeCount++ : NONE;
    if (keep) nodesFile.put(nodes[i], nodes[i + 1]);
  }
  const edgesFd = fs.openSync(edgesPath, "r");
  const shapesFd = fs.openSync(shapesPath, "r");
  const totalPoints = fs.fstatSync(shapesFd).size / 8;
  const totalEdges = fs.fstatSync(edgesFd).size / (EDGE_WORDS * 4);
  let buffer = Buffer.alloc(LONGEST_WAY * 8);
  let edgeCount = 0;
  let points = 0;
  for (const { words, count, last } of edgeChunks(edgesFd, totalEdges)) {
    for (let e = 0; e < count; e++) {
      const at = e * EDGE_WORDS;
      const from = local[words[at]];
      const to = local[words[at + 1]];
      if (from === NONE || to === NONE) continue;
      const start = words[at + 5];
      const end =
        last && e === count - 1 ? totalPoints : words[at + EDGE_WORDS + 5];
      const size = (end - start) * 8;
      if (size > buffer.length) buffer = Buffer.alloc(size);
      fs.readSync(shapesFd, buffer, 0, size, start * 8);
      shapesFile.putBytes(buffer.subarray(0, size));
      edgesFile.put(
        from,
        to,
        words[at + 2],
        words[at + 3],
        words[at + 4],
        points,
      );
      points += end - start;
      edgeCount++;
    }
  }
  fs.closeSync(edgesFd);
  fs.closeSync(shapesFd);
  nodesFile.close();
  edgesFile.close();
  shapesFile.close();
  return {
    nodes: nodeCount,
    edges: edgeCount,
    points,
    bytes: nodesFile.bytes + edgesFile.bytes + shapesFile.bytes,
  };
}

// Pass 4: one state at a time, so memory is one lookup table however many
// states there are. A road near a border lands in both states' files.
export function splitStates(nationalDir, outlinesDir, outDir, marginKm) {
  const nodes = loadInts(`${nationalDir}/nodes.bin`);
  const local = new Uint32Array(nodes.length / 2);
  const national = {
    nodes,
    edgesPath: `${nationalDir}/edges.bin`,
    shapesPath: `${nationalDir}/shapes.bin`,
  };
  const states = {};
  for (const file of fs.readdirSync(outlinesDir).sort()) {
    if (!file.endsWith(".poly")) continue;
    const name = file.slice(0, -".poly".length);
    const rings = readRings(`${outlinesDir}/${file}`);
    const grid = new StateGrid(rings, marginKm);
    states[name] = splitState(national, `${outDir}/${name}`, grid, local);
  }
  return states;
}

export function buildStates(pbfPath, outlinesDir, outDir, marginKm) {
  const nationalDir = `${outDir}/.road-build-national`;
  fs.mkdirSync(nationalDir, { recursive: true });
  const result = build(pbfPath, nationalDir);
  const states = splitStates(nationalDir, outlinesDir, outDir, marginKm);
  fs.rmSync(nationalDir, { recursive: true, force: true });
  return { ...result, states };
}

if (process.argv[1] === fileURLToPath(import.meta.url)) {
  const [pbfPath, outlinesDir, outDir] = process.argv.slice(2);
  if (!pbfPath || !outlinesDir || !outDir) {
    console.error(
      "usage: node scripts/road-build.mjs <file.osm.pbf> <outlines folder> <output folder>",
    );
    process.exit(1);
  }
  fs.mkdirSync(outDir, { recursive: true });
  const started = Date.now();
  const { states, ...result } = buildStates(
    pbfPath,
    outlinesDir,
    outDir,
    MARGIN_KM,
  );
  const seconds = (Date.now() - started) / 1000;
  const peak = Math.round(process.resourceUsage().maxRSS / 1024);
  for (const [name, state] of Object.entries(states)) {
    const megabytes = Math.round(state.bytes / 1e6);
    console.log(
      `${name}: ${state.nodes} nodes, ${state.edges} edges, ${megabytes}MB`,
    );
  }
  console.log({ ...result, seconds, peakMB: peak });
}
