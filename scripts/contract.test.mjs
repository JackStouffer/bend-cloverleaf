import { test } from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { validate, operation, conforms } from "./contract.mjs";

const spec = JSON.parse(readFileSync(new URL("../backend/openapi.json", import.meta.url), "utf8"));
const appraisal = {
  id: "a1",
  key: "k",
  address: "1 Main St",
  zip: "78701",
  state: "TX",
  due: "2026-12-01",
  status: "open",
};
const ref = { $ref: "#/components/schemas/Appraisal" };
const json = "application/json";

test("an appraisal validates, and a wrong one doesn't", () => {
  assert.deepEqual(validate(spec, ref, appraisal), []);
  assert.equal(validate(spec, ref, { ...appraisal, status: "lost" }).length, 1);
  assert.equal(validate(spec, ref, { ...appraisal, extra: 1 }).length, 1);
  const { id, ...noId } = appraisal;
  assert.equal(id, "a1");
  assert.equal(validate(spec, ref, noId).length, 1);
  assert.equal(validate(spec, ref, { ...appraisal, zip: 78701 }).length, 1);
});

test("paths match their templates and give their parameters", () => {
  const found = operation(spec, "POST", "/api/v1/appraisals/a7/cancel");
  assert.equal(found.template, "/api/v1/appraisals/{id}/cancel");
  assert.deepEqual(found.params, { id: "a7" });
  assert.equal(operation(spec, "GET", "/api/v1/appraisals/a7/x"), undefined);
  assert.equal(operation(spec, "DELETE", "/api/v1/appraisals/a7").op, undefined);
});

test("a response is held to its route's answers", () => {
  const body = JSON.stringify(appraisal);
  const err = JSON.stringify({ error: "not_found" });
  assert.deepEqual(conforms(spec, "GET", "/api/v1/appraisals/a1", 200, json, body), []);
  assert.deepEqual(conforms(spec, "GET", "/api/v1/appraisals/a1", 404, json, err), []);
  assert.deepEqual(conforms(spec, "GET", "/api/v1/appraisals/a1", 400, json, err), []);
  assert.equal(conforms(spec, "GET", "/api/v1/appraisals/a1", 201, json, body).length, 1);
  assert.equal(conforms(spec, "GET", "/api/v1/appraisals/a1", 200, json, err).length > 0, true);
  assert.equal(conforms(spec, "GET", "/api/v1/appraisals/a1", 500, json, err).length, 1);
  assert.equal(conforms(spec, "GET", "/api/v1/appraisals/a1", 200, "text/html", body).length, 1);
  assert.deepEqual(conforms(spec, "DELETE", "/api/v1/appraisals/a1", 405, json, JSON.stringify({ error: "method_not_allowed" })), []);
  assert.deepEqual(conforms(spec, "GET", "/api/nope", 404, json, JSON.stringify({ error: "not_found" })), []);
});
