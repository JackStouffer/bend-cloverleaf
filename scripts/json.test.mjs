// Checks the Bend JSON printer and parser in backend/web/json.bend against
// JavaScript's own JSON. The codec laws reason about the JSON tree, so this is
// what covers the text on either side of it. It builds the module with bend,
// and skips when bend isn't on PATH.
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { mkdtempSync, rmSync } from "node:fs";
import { tmpdir } from "node:os";
import { dirname, join } from "node:path";
import test from "node:test";
import { fileURLToPath, pathToFileURL } from "node:url";

const backend = join(dirname(fileURLToPath(import.meta.url)), "..", "backend");
const found = spawnSync("bend", ["--version"], { encoding: "utf8" });
const skip = found.error === undefined ? false : "bend is not on PATH";

async function load() {
  const dir = mkdtempSync(join(tmpdir(), "cloverleaf-json-"));
  try {
    const out = join(dir, "json.mjs");
    const run = spawnSync("bend", ["web/json.bend", "-o", out], {
      cwd: backend,
      encoding: "utf8",
      env: { ...process.env, BEND_NO_TELEMETRY: "1" },
    });
    assert.equal(run.status, 0, run.stdout + run.stderr);
    return (await import(pathToFileURL(out).href)).default;
  } finally {
    rmSync(dir, { recursive: true, force: true });
  }
}

// A small seeded generator, so a failure reproduces.
function rng(seed) {
  let s = seed >>> 0;
  return () => {
    s = (Math.imul(s, 1664525) + 1013904223) >>> 0;
    return s / 2 ** 32;
  };
}

const chars = ["a", "Z", "0", " ", '"', "\\", "/", "\n", "\t", "\b", "\f", "\r", "\u0001", "\u001f", "\u007f", "é", "中", "😀", " "];

function value(r, depth) {
  const pick = Math.floor(r() * (depth > 3 ? 5 : 7));
  switch (pick) {
    case 0:
      return null;
    case 1:
      return r() < 0.5;
    case 2:
      return Math.floor(r() * 10 ** Math.floor(r() * 15));
    case 3:
    case 4:
      return Array.from({ length: Math.floor(r() * 6) }, () => chars[Math.floor(r() * chars.length)]).join("");
    case 5:
      return Array.from({ length: Math.floor(r() * 4) }, () => value(r, depth + 1));
    default: {
      const o = {};
      for (let i = Math.floor(r() * 4); i > 0; i--) o[value(r, 9) + String(i)] = value(r, depth + 1);
      return o;
    }
  }
}

test("prints what it parses the way JSON.stringify does", { skip }, async () => {
  const J = await load();
  const r = rng(7);
  for (let i = 0; i < 400; i++) {
    const v = value(r, 0);
    const text = JSON.stringify(v);
    const parsed = J["Json.parse"](text);
    assert.equal(parsed.$, "Some", text);
    assert.equal(J["Json.print"](parsed.value), text);
    assert.equal(J["Json.pretty"](parsed.value, 0, ""), JSON.stringify(v, null, 2));
  }
});

test("reads whitespace and escapes JSON allows", { skip }, async () => {
  const J = await load();
  for (const text of [' { "a" : [ 1 , 2 ] }\n', '"\\u00e9\\ud83d\\ude00\\/"', "[[],{}]"]) {
    const parsed = J["Json.parse"](text);
    assert.equal(parsed.$, "Some", text);
    assert.equal(J["Json.print"](parsed.value), JSON.stringify(JSON.parse(text)));
  }
});

test("refuses broken JSON and numbers outside whole 14-digit Nats", { skip }, async () => {
  const J = await load();
  for (const text of ["", "01", "1.5", "1e3", "-1", "123456789012345", "[1,]", "{\"a\" 1}", "{\"a\":1,}", "tru", "nul", '"\\ud83d"', '"\\x"', "\"a\u0001\"", "[1] 2", "{1:2}"]) {
    assert.equal(J["Json.parse"](text).$, "None", text);
  }
});
