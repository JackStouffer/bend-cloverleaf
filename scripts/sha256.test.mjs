// Checks the Bend SHA-256 in backend/web/sha256.bend against Node's crypto.
// The web process stores only the hash of each API key, so a wrong digest
// would lock every dealer out. It builds the module with bend, and skips when
// bend isn't on PATH.
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { createHash } from "node:crypto";
import { mkdtempSync, rmSync } from "node:fs";
import { tmpdir } from "node:os";
import { dirname, join } from "node:path";
import test from "node:test";
import { fileURLToPath, pathToFileURL } from "node:url";

const backend = join(dirname(fileURLToPath(import.meta.url)), "..", "backend");
const found = spawnSync("bend", ["--version"], { encoding: "utf8" });
const skip = found.error === undefined ? false : "bend is not on PATH";

async function load() {
  const dir = mkdtempSync(join(tmpdir(), "cloverleaf-sha-"));
  try {
    const out = join(dir, "sha256.mjs");
    const run = spawnSync("bend", ["web/sha256.bend", "-o", out], {
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

const sha = (s) => createHash("sha256").update(s, "ascii").digest("hex");

// A small seeded generator, so a failure reproduces.
function rng(seed) {
  let s = seed >>> 0;
  return () => {
    s = (Math.imul(s, 1664525) + 1013904223) >>> 0;
    return s / 2 ** 32;
  };
}

test("hashes every length from 0 to 200 bytes the way Node does", { skip }, async () => {
  const H = await load();
  const r = rng(11);
  // Lengths 55, 56, 63, 64 and 119, 120 cross the padding's block edges.
  for (let n = 0; n <= 200; n++) {
    const text = Array.from({ length: n }, () => String.fromCharCode(32 + Math.floor(r() * 95))).join("");
    assert.equal(H["Sha.text"](text), sha(text), JSON.stringify(text));
  }
});

test("hashes keys shaped like the ones it issues", { skip }, async () => {
  const H = await load();
  const r = rng(3);
  for (let i = 0; i < 50; i++) {
    const key = "clv_" + Array.from({ length: 64 }, () => Math.floor(r() * 16).toString(16)).join("");
    assert.equal(H["Sha.text"](key), sha(key), key);
  }
});
