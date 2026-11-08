import assert from "node:assert/strict";
import test from "node:test";
import { allowedDepth, readMatrix } from "./nightly.mjs";

test("reads the depth the road process allows from its refusal", () => {
  assert.equal(allowedDepth("lane depth 3 won't fit: a lane takes 536MB and the budget allows depth 0"), 0);
  assert.equal(allowedDepth("lane depth 3 won't fit: a lane takes 140MB and the budget allows depth 2\n"), 2);
  assert.equal(allowedDepth("could not write the matrix"), null);
});

test("reads a matrix file: a count, then a word per pair in row order", () => {
  const words = Uint32Array.from([2, 0, 600, 4294967295, 0]);
  const m = readMatrix(new Uint8Array(words.buffer));
  assert.equal(m.count, 2);
  assert.equal(m.at(0, 1), 600);
  assert.equal(m.at(1, 0), null);
  assert.equal(m.reached, 3);
});
