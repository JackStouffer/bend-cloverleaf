import { test } from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { validate, operation, conforms, envValue, keptProblem } from "./contract.mjs";

const spec = JSON.parse(readFileSync(new URL("../backend/openapi.json", import.meta.url), "utf8"));
const appraisal = {
  id: "a1",
  organization: "o1",
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
  assert.deepEqual(operation(spec, "GET", "/api/v1/appraisals/a%207").params, { id: "a%207" });
  assert.deepEqual(operation(spec, "GET", "/api/v1/appraisals/%E0").params, { id: "%E0" });
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
  const unsaved = JSON.stringify({ error: "not_saved" });
  assert.deepEqual(conforms(spec, "POST", "/api/v1/appraisals", 500, json, unsaved), []);
  assert.deepEqual(conforms(spec, "POST", "/api/v1/appraisals/a1/cancel", 500, json, unsaved), []);
  assert.equal(conforms(spec, "GET", "/api/health", 500, json, unsaved).length, 1);
  assert.equal(conforms(spec, "GET", "/api/v1/appraisals/a1", 200, "text/html", body).length, 1);
  assert.deepEqual(conforms(spec, "DELETE", "/api/v1/appraisals/a1", 405, json, JSON.stringify({ error: "method_not_allowed" })), []);
  assert.deepEqual(conforms(spec, "GET", "/api/nope", 404, json, JSON.stringify({ error: "not_found" })), []);
});

test("the gate's answers and a new organization's key conform", () => {
  const unauthorized = JSON.stringify({ error: "unauthorized" });
  const forbidden = JSON.stringify({ error: "forbidden" });
  assert.deepEqual(conforms(spec, "GET", "/api/v1/appraisals/a1", 401, json, unauthorized), []);
  assert.deepEqual(conforms(spec, "POST", "/api/v1/organizations", 403, json, forbidden), []);
  const made = { id: "o3", name: "Cedar", apiKey: `clv_${"ab".repeat(32)}` };
  assert.deepEqual(conforms(spec, "POST", "/api/v1/organizations", 201, json, JSON.stringify(made)), []);
  assert.equal(conforms(spec, "POST", "/api/v1/organizations", 201, json, JSON.stringify({ ...made, keyHash: "x" })).length, 1);
  assert.deepEqual(spec.paths["/api/health"].get.security, []);
  assert.deepEqual(spec.paths["/api/v1/organizations"].post.security, [{ adminKey: [] }]);
});

test("reads a value out of a .env file", () => {
  const text = "# local\nOTHER=1\nexport CLOVERLEAF_ADMIN_KEY = 'abc def' \n";
  assert.equal(envValue(text, "CLOVERLEAF_ADMIN_KEY"), "abc def");
  assert.equal(envValue("CLOVERLEAF_ADMIN_KEY=abc # note\n", "CLOVERLEAF_ADMIN_KEY"), "abc");
  assert.equal(envValue('CLOVERLEAF_ADMIN_KEY="x=y"', "CLOVERLEAF_ADMIN_KEY"), "x=y");
  assert.equal(envValue("OTHER=1", "CLOVERLEAF_ADMIN_KEY"), undefined);
  assert.equal(envValue('CLOVERLEAF_ADMIN_KEY="abc" # admin', "CLOVERLEAF_ADMIN_KEY"), "abc");
  assert.equal(envValue("CLOVERLEAF_ADMIN_KEY='abc'   # admin", "CLOVERLEAF_ADMIN_KEY"), "abc");
});

test("a keep file from before organizations is refused with a plain problem", () => {
  assert.match(keptProblem([{ id: "a1" }]), /older contract run/);
  assert.match(keptProblem({ appraisals: [{ id: "a1" }] }), /older contract run/);
  assert.match(keptProblem(null), /older contract run/);
  assert.match(keptProblem({ key: "clv_a", other: "clv_b", appraisals: [{ id: "a1" }] }), /older contract run/);
  assert.equal(keptProblem({ key: "clv_a", other: "clv_b", revoked: ["clv_c"], appraisals: [{ id: "a1" }] }), undefined);
});
