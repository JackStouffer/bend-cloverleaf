import assert from "node:assert/strict";
import test from "node:test";
import {
  STATES,
  apportion,
  coverZips,
  decodeInstance,
  encodeInstance,
  makeCrew,
  makeJob,
  random,
  toCore,
  zipOf,
} from "./synth.mjs";

test("lists the lower 48 and DC, each with a FIPS code and a population", () => {
  assert.equal(STATES.length, 49);
  assert.equal(new Set(STATES.map((s) => s.fips)).size, 49);
  const texas = STATES.find((s) => s.name === "texas");
  assert.equal(texas.fips, 48);
  assert.ok(STATES.every((s) => s.population > 500000));
});

test("apportions a total by weight, with a floor for every share", () => {
  const shares = apportion(10, [1, 1, 8], 1);
  assert.deepEqual(shares, [1, 1, 8]);
  const big = apportion(1000, STATES.map((s) => s.population), 1);
  assert.equal(big.reduce((a, b) => a + b, 0), 1000);
  assert.ok(big.every((n) => n >= 1));
  const tx = big[STATES.findIndex((s) => s.name === "texas")];
  assert.ok(tx > 80 && tx < 95, `texas got ${tx}`);
});

test("random is repeatable for a seed", () => {
  const a = random(7);
  const b = random(7);
  const xs = [a(), a(), a()];
  assert.deepEqual(xs, [b(), b(), b()]);
  assert.ok(xs.every((x) => x >= 0 && x < 1));
  assert.notDeepEqual(xs, [random(8)(), random(8)(), random(8)()]);
});

test("rounds coordinates to the core's units: 1e-4 degrees, longitude west", () => {
  assert.deepEqual(toCore(407128000, -740060000), { lat: 407128, lon: 740060 });
  assert.deepEqual(toCore(407128490, -740060510), { lat: 407128, lon: 740061 });
});

test("a zip is a 0.1 degree cell inside its state", () => {
  const a = zipOf(36, { lat: 407128, lon: 740060 });
  assert.equal(a, zipOf(36, { lat: 407999, lon: 740999 }));
  assert.notEqual(a, zipOf(36, { lat: 408000, lon: 740060 }));
  assert.notEqual(a, zipOf(36, { lat: 407128, lon: 741000 }));
  assert.notEqual(a, zipOf(13, { lat: 407128, lon: 740060 }));
  assert.ok(a < 2 ** 32);
});

test("every cell goes to its nearest contractor, and a near tie to both", () => {
  const homes = [
    { lat: 400000, lon: 1000000 },
    { lat: 400000, lon: 1010000 },
    { lat: 450000, lon: 1000000 },
  ];
  const cells = [
    { lat: 400000, lon: 1005000 }, // halfway between the first two
    { lat: 449000, lon: 1000000 }, // next to the third
    { lat: 400000, lon: 999000 }, // just past the first
  ];
  const zips = coverZips(homes, cells, [11, 12, 13], 0);
  assert.deepEqual(zips[0], [11, 13]);
  assert.deepEqual(zips[1], [11]);
  assert.deepEqual(zips[2], [12]);
});

test("a contractor also covers every cell within its radius", () => {
  // The cell is 34km from the second home and 51km from the first.
  const homes = [{ lat: 400000, lon: 1000000 }, { lat: 400000, lon: 1010000 }];
  const cells = [{ lat: 400000, lon: 1006000 }];
  assert.deepEqual(coverZips(homes, cells, [7], 0), [[], [7]]);
  assert.deepEqual(coverZips(homes, cells, [7], 60), [[7], [7]]);
});

test("a contractor works some days of the horizon, in order, at their hours", () => {
  const rand = random(3);
  for (let i = 0; i < 200; i++) {
    const c = makeCrew(rand, i + 1, { lat: 1, lon: 2 }, 20000, 7);
    assert.ok(c.days.length >= 4 && c.days.length <= 6, `${c.days}`);
    assert.deepEqual([...c.days].sort((a, b) => a - b), c.days);
    assert.ok(c.days.every((d) => d >= 20000 && d < 20007));
    assert.ok([360, 420, 480, 540, 600].includes(c.maxMinutes));
  }
});

test("jobs are due across the horizon and past it, and take 15 to 30 minutes", () => {
  const rand = random(5);
  const dues = new Map();
  for (let i = 0; i < 2000; i++) {
    const j = makeJob(rand, i + 1, { lat: 1, lon: 2 }, 99, 20000, 7);
    assert.ok([15, 20, 30].includes(j.minutes));
    dues.set(j.due - 20000, (dues.get(j.due - 20000) ?? 0) + 1);
  }
  assert.ok(dues.get(0) > 100, "some are due today");
  assert.ok([...dues.keys()].some((d) => d >= 7), "some can wait past the horizon");
  assert.ok([...dues.keys()].every((d) => d >= 0 && d < 14));
});

test("an instance round-trips through its file format, days as a mask", () => {
  const inst = {
    state: 10,
    cap: 60,
    first: 20000,
    days: 7,
    crews: [
      { id: 1, home: { lat: 390000, lon: 755000 }, zips: [5, 9], maxMinutes: 480, days: [20000, 20002] },
      { id: 4, home: { lat: 391000, lon: 756000 }, zips: [], maxMinutes: 360, days: [20006] },
    ],
    jobs: [{ id: 3, site: { lat: 392000, lon: 757000 }, zip: 9, due: 20003, minutes: 20 }],
  };
  const words = encodeInstance(inst);
  assert.ok(words instanceof Uint32Array);
  assert.deepEqual(decodeInstance(words), inst);
  // header, then id, lat, lon, max minutes, day mask, zip count, zips
  assert.deepEqual([...words.slice(7, 15)], [1, 390000, 755000, 480, 0b101, 2, 5, 9]);
});
