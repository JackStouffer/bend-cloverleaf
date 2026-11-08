import assert from "node:assert/strict";
import test from "node:test";
import {
  GIVE_WAY,
  SIGNALS,
  STOP_MINOR,
  components,
  deviation,
  keptNodes,
  obstacleOf,
  turnSeconds,
  writeTurns,
} from "./road-turns.mjs";

const NONE = 2 ** 32 - 1;
const tags = (object) => new Map(Object.entries(object));

test("costs turns like OSRM: right cheaper than left, straight almost free", () => {
  assert.ok(turnSeconds(0) < 0.01);
  assert.equal(+turnSeconds(90).toFixed(2), 2.11);
  assert.equal(+turnSeconds(-90).toFixed(2), 5.39);
  assert.equal(deviation(0, 90), 90);
  assert.equal(deviation(0, 270), -90);
  assert.equal(deviation(350, 10), 20);
});

test("reads obstacles and their directions from node tags", () => {
  assert.equal(obstacleOf(tags({ highway: "traffic_signals" })), SIGNALS);
  assert.equal(
    obstacleOf(
      tags({
        highway: "traffic_signals",
        "traffic_signals:direction": "backward",
      }),
    ),
    SIGNALS | (2 << 3),
  );
  assert.equal(
    obstacleOf(tags({ highway: "stop", stop: "minor" })),
    STOP_MINOR,
  );
  assert.equal(
    obstacleOf(tags({ highway: "give_way", direction: "forward" })),
    GIVE_WAY | (1 << 3),
  );
  assert.equal(obstacleOf(tags({ highway: "crossing" })), 0);
});

// Edges given as [from, to, twoWay, deciseconds, leaving, arriving].
function edges(list, extra = {}) {
  return {
    count: list.length,
    from: (k) => list[k][0],
    to: (k) => list[k][1],
    twoWay: (k) => list[k][2],
    deciseconds: (k) => list[k][3],
    leaving: (k) => list[k][4] ?? 0,
    arriving: (k) => list[k][5] ?? 0,
    speed: (k) => extra.speed?.(k) ?? 10,
    reversed: () => false,
    delay: () => 0,
  };
}

test("finds a one-way trap as its own small piece and drops it", () => {
  // 0, 1 and 2 form a loop; 3 can be reached from 2 but leads nowhere.
  const graph = edges([
    [0, 1, true, 10],
    [1, 2, true, 10],
    [2, 0, true, 10],
    [2, 3, false, 10],
  ]);
  const { renumber, kept } = keptNodes(4, graph, 2, NONE);
  assert.equal(kept, 3);
  assert.deepEqual([...renumber], [0, 1, 2, NONE]);
  const first = new Uint32Array([0, 1, 2, 3, 3]);
  const items = new Uint32Array([0, 1, 2]);
  const { sizes } = components(4, { first, items, head: (i) => [1, 2, 0][i] });
  assert.deepEqual(sizes.sort(), [1, 3]);
});

// A crossroads at 0, with roads north to 1, east to 2, south to 3 and west to 4.
// Bearings are in degrees, so the road from 3 arrives at 0 heading north.
function crossroads(signals) {
  const roads = edges([
    [0, 1, true, 100, 0, 0],
    [0, 2, true, 100, 90, 90],
    [3, 0, true, 100, 0, 0],
    [0, 4, true, 100, 270, 270],
  ]);
  const arcs = [];
  const result = writeTurns(
    5,
    roads,
    (v) => (v === 0 && signals ? SIGNALS : 0),
    (a, b, c) => arcs.push([a, b, c]),
  );
  // Directions: 0 is 0->1, 1 is 1->0, 2 is 0->2, 3 is 2->0, 4 is 3->0, 5 is
  // 0->3, 6 is 0->4, 7 is 4->0.
  const cost = (a, b) => arcs.find(([x, y]) => x === a && y === b)?.[2];
  return { result, arcs, cost };
}

test("charges each turn at a crossroads, and the road taken", () => {
  const { cost } = crossroads(false);
  assert.equal(cost(4, 0), 100);
  assert.equal(cost(4, 2), 100 + 21);
  assert.equal(cost(4, 6), 100 + 54);
  assert.equal(cost(4, 5), undefined);
});

test("allows a U-turn only at a dead end, with OSRM's penalty", () => {
  const { cost } = crossroads(false);
  assert.equal(cost(0, 1), 100 + 275);
});

test("adds a traffic signal to every turn through it", () => {
  const { cost } = crossroads(true);
  assert.equal(cost(4, 0), 100 + 20);
  assert.equal(cost(4, 2), 100 + 21 + 20);
});

test("links each junction's depart and arrive nodes to its roads", () => {
  const { result, cost } = crossroads(false);
  const d = result.directions;
  assert.equal(d, 8);
  assert.equal(cost(d + 3, 4), 100);
  assert.equal(cost(4, d + 5 + 0), 0);
  assert.equal(cost(d + 0, d + 5 + 0), 0);
});
