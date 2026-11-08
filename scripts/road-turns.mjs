// Turn costs and cut-off pieces of one state's road graph, for road-build.mjs,
// whose header defines turns.bin. To the Bend search the turn graph is an
// ordinary graph, so its laws hold unchanged.
//
// Turn costs and obstacle delays follow OSRM's car profile, Copyright (c) 2017,
// Project OSRM contributors, under the BSD license in OSRM-LICENSE.txt. OSRM
// also drops small cut-off pieces of the graph so that stops never snap to them.

// OSRM won't snap to a component smaller than this, and we drop them.
export const SMALL_COMPONENT = 1000;

const TURN_PENALTY = 7.5;
const TURN_BIAS = 1.075;
const U_TURN_PENALTY = 20;

// Obstacle codes: a type in the low 3 bits and a direction above them, relative
// to the way's drawn order.
export const SIGNALS = 1;
export const STOP = 2;
export const STOP_MINOR = 3;
export const GIVE_WAY = 4;
const FORWARD = 1;
const BACKWARD = 2;
const OBSTACLE_SECONDS = [0, 2, 2, 2, 1];

export function obstacleOf(tags) {
  const highway = tags.get("highway");
  let type = 0;
  if (highway === "traffic_signals") type = SIGNALS;
  else if (highway === "stop")
    type = tags.get("stop") === "minor" ? STOP_MINOR : STOP;
  else if (highway === "give_way") type = GIVE_WAY;
  if (type === 0) return 0;
  const direction =
    (type === SIGNALS ? tags.get("traffic_signals:direction") : undefined) ??
    tags.get("direction");
  const way =
    direction === "forward" ? FORWARD : direction === "backward" ? BACKWARD : 0;
  return type | (way << 3);
}

// Whether an obstacle holds up travel along or against the way's drawn order.
export function obstacleApplies(code, along) {
  const way = code >>> 3;
  return way === 0 || (way === FORWARD) === along;
}

// Deciseconds an obstacle on a road's middle adds, in one direction. A minor
// road's stop sign needs a junction, so it adds nothing here.
export function passingDelay(code, along) {
  const type = code & 7;
  if (type === 0 || type === STOP_MINOR || !obstacleApplies(code, along))
    return 0;
  return OBSTACLE_SECONDS[type] * 10;
}

// Initial bearing in whole degrees clockwise from north, between points in
// degrees * 1e7.
export function bearing(lat1, lon1, lat2, lon2) {
  const toRadians = Math.PI / 180 / 1e7;
  const a = lat1 * toRadians;
  const b = lat2 * toRadians;
  const dLon = (lon2 - lon1) * toRadians;
  const y = Math.sin(dLon) * Math.cos(b);
  const x =
    Math.cos(a) * Math.sin(b) - Math.sin(a) * Math.cos(b) * Math.cos(dLon);
  return Math.round(((Math.atan2(y, x) * 180) / Math.PI + 360) % 360) % 360;
}

// How far a turn swings from straight on, in degrees: right is positive.
export function deviation(arriving, leaving) {
  const d = (((leaving - arriving) % 360) + 360) % 360;
  return d > 180 ? d - 360 : d;
}

// OSRM's turn cost in seconds: almost nothing straight on, about 2 for a right
// turn and 5 for a left, in right-hand traffic.
export function turnSeconds(angle) {
  if (angle >= 0) {
    return (
      TURN_PENALTY /
      (1 + Math.exp(-((13 / TURN_BIAS) * (angle / 180) - 6.5 * TURN_BIAS)))
    );
  }
  return (
    TURN_PENALTY /
    (1 + Math.exp(-(13 * TURN_BIAS * (-angle / 180) - 6.5 / TURN_BIAS)))
  );
}

// Growable typed arrays, so a state's edges cost 4 bytes a field.
export class Column {
  constructor(Kind = Uint32Array) {
    this.Kind = Kind;
    this.data = new Kind(1024);
    this.length = 0;
  }

  push(value) {
    if (this.length === this.data.length) {
      const grown = new this.Kind(this.data.length * 2);
      grown.set(this.data);
      this.data = grown;
    }
    this.data[this.length++] = value;
  }
}

function adjacency(n, count, tail, head) {
  const first = new Uint32Array(n + 1);
  for (let i = 0; i < count; i++) first[tail(i) + 1]++;
  for (let v = 0; v < n; v++) first[v + 1] += first[v];
  const next = first.slice(0, n);
  const items = new Uint32Array(count);
  for (let i = 0; i < count; i++) items[next[tail(i)]++] = i;
  return { first, items, head };
}

// Strongly connected components by Tarjan's method, without recursion. Returns
// each node's component and each component's size.
export function components(n, graph) {
  const { first, items, head } = graph;
  const index = new Int32Array(n).fill(-1);
  const low = new Uint32Array(n);
  const onStack = new Uint8Array(n);
  const component = new Int32Array(n).fill(-1);
  const stack = new Uint32Array(n);
  const calls = new Uint32Array(n);
  const cursor = new Uint32Array(n);
  const sizes = [];
  let counter = 0;
  let top = 0;
  for (let root = 0; root < n; root++) {
    if (index[root] >= 0) continue;
    let depth = 0;
    calls[depth++] = root;
    index[root] = low[root] = counter++;
    cursor[root] = first[root];
    stack[top++] = root;
    onStack[root] = 1;
    while (depth > 0) {
      const v = calls[depth - 1];
      if (cursor[v] < first[v + 1]) {
        const w = head(items[cursor[v]++]);
        if (index[w] < 0) {
          index[w] = low[w] = counter++;
          cursor[w] = first[w];
          stack[top++] = w;
          onStack[w] = 1;
          calls[depth++] = w;
        } else if (onStack[w] && index[w] < low[v]) {
          low[v] = index[w];
        }
        continue;
      }
      depth--;
      if (depth > 0) {
        const parent = calls[depth - 1];
        if (low[v] < low[parent]) low[parent] = low[v];
      }
      if (low[v] === index[v]) {
        const id = sizes.length;
        let size = 0;
        let w;
        do {
          w = stack[--top];
          onStack[w] = 0;
          component[w] = id;
          size++;
        } while (w !== v);
        sizes.push(size);
      }
    }
  }
  return { component, sizes };
}

// Directed roads: each edge forwards, then backwards if it's two-way.
function directions(edges) {
  const { count, from, to, twoWay } = edges;
  let total = 0;
  for (let k = 0; k < count; k++) total += twoWay(k) ? 2 : 1;
  const edge = new Uint32Array(total);
  const back = new Uint8Array(total);
  let d = 0;
  for (let k = 0; k < count; k++) {
    edge[d++] = k;
    if (twoWay(k)) {
      edge[d] = k;
      back[d++] = 1;
    }
  }
  const tail = (i) => (back[i] ? to(edge[i]) : from(edge[i]));
  const head = (i) => (back[i] ? from(edge[i]) : to(edge[i]));
  return { total, edge, back, tail, head };
}

// Which nodes to keep: those in a strongly connected piece of at least `least`
// nodes. Returns new numbers in the old order, or NONE.
export function keptNodes(n, edges, least, NONE) {
  const ways = directions(edges);
  const { component, sizes } = components(
    n,
    adjacency(n, ways.total, ways.tail, ways.head),
  );
  const renumber = new Uint32Array(n);
  let kept = 0;
  for (let v = 0; v < n; v++) {
    renumber[v] = sizes[component[v]] >= least ? kept++ : NONE;
  }
  return { renumber, kept };
}

// Writes the turn graph through put(from, to, deciseconds). `edges` gives each
// edge's ends, two-way flag, deciseconds and speed, its bearings leaving `from`
// and reaching `to`, its delays from obstacles part way along in each direction,
// and whether it runs against its way's drawn order. `obstacles` gives each
// junction's obstacle code. Returns the number of arcs.
export function writeTurns(n, edges, obstacles, put) {
  const ways = directions(edges);
  const { total, edge, back, tail, head } = ways;
  const out = adjacency(n, total, tail, head);
  const into = adjacency(n, total, head, tail);
  const cost = (i) =>
    edges.deciseconds(edge[i]) + edges.delay(edge[i], back[i] === 1);
  const leaving = (i) =>
    back[i] ? (edges.arriving(edge[i]) + 180) % 360 : edges.leaving(edge[i]);
  const arriving = (i) =>
    back[i] ? (edges.leaving(edge[i]) + 180) % 360 : edges.arriving(edge[i]);
  const along = (i) => (back[i] === 1) === edges.reversed(edge[i]);
  let arcs = 0;
  const arc = (a, b, deciseconds) => {
    put(a, b, Math.min(deciseconds, 4294967294));
    arcs++;
  };
  for (let v = 0; v < n; v++) {
    const roads = new Set();
    for (let j = out.first[v]; j < out.first[v + 1]; j++)
      roads.add(edge[out.items[j]]);
    for (let j = into.first[v]; j < into.first[v + 1]; j++)
      roads.add(edge[into.items[j]]);
    const exits = out.first[v + 1] - out.first[v];
    const code = obstacles(v);
    for (let j = out.first[v]; j < out.first[v + 1]; j++) {
      const b = out.items[j];
      arc(total + v, b, cost(b));
    }
    for (let j = into.first[v]; j < into.first[v + 1]; j++) {
      const a = into.items[j];
      arc(a, total + n + v, 0);
      let held = 0;
      if (code !== 0 && obstacleApplies(code, along(a))) {
        const type = code & 7;
        if (type !== STOP_MINOR) held = OBSTACLE_SECONDS[type];
        else {
          let fastest = 0;
          for (const k of roads) {
            if (k !== edge[a]) fastest = Math.max(fastest, edges.speed(k));
          }
          if (fastest > edges.speed(edge[a])) held = OBSTACLE_SECONDS[type];
        }
      }
      for (let i = out.first[v]; i < out.first[v + 1]; i++) {
        const b = out.items[i];
        const uTurn = edge[b] === edge[a] && back[b] !== back[a];
        if (uTurn && exits > 1) continue;
        let seconds = held;
        if (roads.size > 2 || uTurn) {
          seconds += turnSeconds(
            uTurn ? 180 : deviation(arriving(a), leaving(b)),
          );
          if (uTurn) seconds += U_TURN_PENALTY;
        }
        arc(a, b, Math.round(seconds * 10) + cost(b));
      }
    }
    arc(total + v, total + n + v, 0);
  }
  return { directions: total, arcs };
}
