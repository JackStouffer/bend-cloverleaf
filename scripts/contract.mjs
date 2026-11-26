// Contract tests: a simulated dealer client talks to the running stack through
// nginx and checks every real response against backend/openapi.json, the spec
// the Bend route table generates.
//
//   node scripts/contract.mjs <base-url> <ca.crt>                  run the contract
//   node scripts/contract.mjs <base-url> <ca.crt> --keep <file>    also save what was created
//   node scripts/contract.mjs <base-url> <ca.crt> --recall <file>  check it all reads back
//
// --keep and --recall make the crash test: keep, kill the web process, wait
// for it to come back, recall. The CA is the stack's own certificate, copied
// out with `docker compose cp nginx:/etc/nginx/certs/tls.crt data/tls.crt`.

import { readFileSync, writeFileSync } from "node:fs";
import { request } from "node:https";
import { randomUUID } from "node:crypto";
import { fileURLToPath } from "node:url";

const SPEC = fileURLToPath(new URL("../backend/openapi.json", import.meta.url));

// The problems with value under schema, as paths and messages. The spec uses a
// small part of JSON Schema: $ref, object with required and closed
// properties, string with enum, integer with bounds, boolean, and array.
export function validate(spec, schema, value, at = "$") {
  if (schema.$ref) {
    const name = schema.$ref.replace("#/components/schemas/", "");
    const target = spec.components?.schemas?.[name];
    if (!target) return [`${at}: unknown $ref ${schema.$ref}`];
    return validate(spec, target, value, at);
  }
  switch (schema.type) {
    case "object": {
      if (value === null || typeof value !== "object" || Array.isArray(value)) return [`${at}: expected an object`];
      const props = schema.properties ?? {};
      const out = [];
      for (const key of schema.required ?? []) if (!(key in value)) out.push(`${at}: missing ${key}`);
      for (const [key, v] of Object.entries(value)) {
        if (key in props) out.push(...validate(spec, props[key], v, `${at}.${key}`));
        else if (schema.additionalProperties === false) out.push(`${at}: unexpected ${key}`);
      }
      return out;
    }
    case "string":
      if (typeof value !== "string") return [`${at}: expected a string`];
      if (schema.enum && !schema.enum.includes(value)) return [`${at}: ${JSON.stringify(value)} is not one of the enum`];
      return [];
    case "integer":
      if (!Number.isInteger(value)) return [`${at}: expected an integer`];
      if (schema.minimum !== undefined && value < schema.minimum) return [`${at}: below ${schema.minimum}`];
      if (schema.maximum !== undefined && value > schema.maximum) return [`${at}: above ${schema.maximum}`];
      return [];
    case "boolean":
      return typeof value === "boolean" ? [] : [`${at}: expected a boolean`];
    case "array":
      if (!Array.isArray(value)) return [`${at}: expected an array`];
      return value.flatMap((v, i) => validate(spec, schema.items, v, `${at}[${i}]`));
    default:
      return [`${at}: the validator doesn't know type ${schema.type}`];
  }
}

// The spec's operation for a method and a concrete path, with its parameters.
export function operation(spec, method, path) {
  const segs = path.split("?")[0].split("/");
  for (const [template, ops] of Object.entries(spec.paths)) {
    const parts = template.split("/");
    if (parts.length !== segs.length) continue;
    const params = {};
    const fits = parts.every((p, i) => {
      if (p.startsWith("{")) {
        params[p.slice(1, -1)] = decodeURIComponent(segs[i]);
        return segs[i] !== "";
      }
      return p === segs[i];
    });
    if (fits) return { template, op: ops[method.toLowerCase()], allowed: Object.keys(ops), params };
  }
  return undefined;
}

// The published answer for a status: its exact code, or the 4XX range.
export function answer(op, status) {
  return op.responses[String(status)] ?? op.responses[`${String(status)[0]}XX`];
}

// Checks one response against the spec. Returns the problems, empty if none.
export function conforms(spec, method, path, status, contentType, body) {
  const found = operation(spec, method, path);
  const errorSchema = { $ref: "#/components/schemas/Error" };
  let schema;
  if (!found) {
    if (status !== 404) return [`${method} ${path}: no such path, so 404 was expected, got ${status}`];
    schema = errorSchema;
  } else if (!found.op) {
    if (status !== 405) return [`${method} ${path}: method not in the spec, so 405 was expected, got ${status}`];
    schema = errorSchema;
  } else {
    const a = answer(found.op, status);
    if (!a) return [`${method} ${found.template}: ${status} isn't a published answer`];
    schema = a.content["application/json"].schema;
  }
  if (!/^application\/json\b/.test(contentType ?? "")) return [`${method} ${path}: content type ${contentType}`];
  let json;
  try {
    json = JSON.parse(body);
  } catch {
    return [`${method} ${path}: body isn't JSON`];
  }
  return validate(spec, schema, json).map((p) => `${method} ${path} ${status}: ${p}`);
}

function send(base, ca, method, path, body) {
  const url = new URL(path, base);
  const data = body === undefined ? undefined : Buffer.from(body);
  return new Promise((resolve, reject) => {
    const req = request(
      url,
      {
        method,
        ca,
        headers: data ? { "content-type": "application/json", "content-length": data.length } : {},
      },
      (res) => {
        const chunks = [];
        res.on("data", (c) => chunks.push(c));
        res.on("end", () =>
          resolve({ status: res.statusCode, type: res.headers["content-type"], text: Buffer.concat(chunks).toString("utf8") }),
        );
      },
    );
    req.on("error", reject);
    req.setTimeout(10000, () => req.destroy(new Error(`${method} ${path} timed out`)));
    req.end(data);
  });
}

function draft(key, overrides = {}) {
  return { key, address: "100 Congress Ave", zip: "78701", state: "TX", due: "2026-12-15", ...overrides };
}

export async function run(base, ca, keep) {
  const spec = JSON.parse(readFileSync(SPEC, "utf8"));
  const problems = [];
  let calls = 0;
  const call = async (method, path, body, expect) => {
    const text = body === undefined ? undefined : typeof body === "string" ? body : JSON.stringify(body);
    const res = await send(base, ca, method, path, text);
    calls += 1;
    problems.push(...conforms(spec, method, path, res.status, res.type, res.text));
    if (expect !== undefined && res.status !== expect) problems.push(`${method} ${path}: expected ${expect}, got ${res.status}`);
    try {
      return { status: res.status, json: JSON.parse(res.text) };
    } catch {
      return { status: res.status, json: undefined };
    }
  };
  const same = (what, a, b) => {
    if (JSON.stringify(a) !== JSON.stringify(b)) problems.push(`${what}: ${JSON.stringify(a)} != ${JSON.stringify(b)}`);
  };

  // A key per run, so the contract can run again against the same log.
  const run = randomUUID().slice(0, 8);
  await call("GET", "/api/health", undefined, 200);

  const first = await call("POST", "/api/v1/appraisals", draft(`${run}-1`), 201);
  const again = await call("POST", "/api/v1/appraisals", draft(`${run}-1`), 200);
  same("a repeated key answers the stored appraisal", again.json, first.json);
  const second = await call("POST", "/api/v1/appraisals", draft(`${run}-2`, { address: "Café Ñandú, 3 Elm" }), 201);
  if (second.json?.id === first.json?.id) problems.push("two keys got one id");

  await call("POST", "/api/v1/appraisals", draft(`${run}-3`, { zip: "7870" }), 422);
  await call("POST", "/api/v1/appraisals", draft(`${run}-3`, { due: "2026-02-31x" }), 422);
  await call("POST", "/api/v1/appraisals", draft(`${run}-3`, { state: "HI" }), 400);
  await call("POST", "/api/v1/appraisals", "{", 400);
  await call("POST", "/api/v1/appraisals", { ...draft(`${run}-3`), extra: 1 }, 400);

  const id = first.json?.id;
  const read = await call("GET", `/api/v1/appraisals/${id}`, undefined, 200);
  same("an appraisal reads back as created", read.json, first.json);
  await call("GET", "/api/v1/appraisals/nope", undefined, 404);
  await call("DELETE", `/api/v1/appraisals/${id}`, undefined, 405);

  const cancelled = await call("POST", `/api/v1/appraisals/${id}/cancel`, undefined, 200);
  same("cancelling changes only the status", cancelled.json, { ...first.json, status: "cancelled" });
  const twice = await call("POST", `/api/v1/appraisals/${id}/cancel`, undefined, 200);
  same("cancelling twice changes nothing", twice.json, cancelled.json);
  await call("POST", "/api/v1/appraisals/nope/cancel", undefined, 404);
  await call("GET", "/api/nope", undefined, 404);

  const after = await call("GET", `/api/v1/appraisals/${second.json?.id}`, undefined, 200);
  same("the other appraisal is untouched", after.json, second.json);

  if (keep) writeFileSync(keep, JSON.stringify([cancelled.json, second.json], null, 2) + "\n");
  return { calls, problems };
}

export async function recall(base, ca, file) {
  const spec = JSON.parse(readFileSync(SPEC, "utf8"));
  const kept = JSON.parse(readFileSync(file, "utf8"));
  const problems = [];
  for (const a of kept) {
    const path = `/api/v1/appraisals/${a.id}`;
    const res = await send(base, ca, "GET", path);
    problems.push(...conforms(spec, "GET", path, res.status, res.type, res.text));
    if (res.status !== 200) problems.push(`${path}: expected 200, got ${res.status}`);
    else if (res.text !== JSON.stringify(a)) problems.push(`${path}: ${res.text} != ${JSON.stringify(a)}`);
  }
  const fresh = await send(base, ca, "POST", "/api/v1/appraisals", JSON.stringify(draft(randomUUID().slice(0, 8))));
  if (fresh.status !== 201) problems.push(`a new request after the restart: expected 201, got ${fresh.status}`);
  else if (kept.some((a) => a.id === JSON.parse(fresh.text).id)) problems.push("an id was reused after the restart");
  return { calls: kept.length + 1, problems };
}

async function main() {
  const [base, caFile, flag, file] = process.argv.slice(2);
  if (!base || !caFile || (flag && !["--keep", "--recall"].includes(flag)) || (flag && !file)) {
    console.error("usage: node scripts/contract.mjs <base-url> <ca.crt> [--keep <file> | --recall <file>]");
    process.exit(2);
  }
  const ca = readFileSync(caFile);
  const { calls, problems } = flag === "--recall" ? await recall(base, ca, file) : await run(base, ca, flag === "--keep" ? file : undefined);
  for (const p of problems) console.error(`FAIL ${p}`);
  console.log(`${calls} requests, ${problems.length} problems`);
  process.exit(problems.length === 0 ? 0 : 1);
}

if (process.argv[1] === fileURLToPath(import.meta.url)) await main();
