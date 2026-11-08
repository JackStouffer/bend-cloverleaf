// Rebuilds the road data the app runs against, from nothing. It fetches the US
// extract and state outlines, builds every state's files beside the current
// ones, checks them, and only then swaps them in, so a failed run leaves the
// current data alone. road-build.mjs defines the format.
//
//   node scripts/rebuild-road-data.mjs [data folder]
//
// The data folder defaults to data, with inputs in data/osm and the result in
// data/road. Each step runs as its own process, so the check shares no code
// with the build. The build peaks at about 750MB: run this under a 1GB cap, as
// the road-build Compose job does, for example with
//
//   systemd-run --user --scope -q -p MemoryMax=1G -p MemorySwapMax=0 \
//     node scripts/rebuild-road-data.mjs
import { spawnSync } from "node:child_process";
import fs from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";

const here = path.dirname(fileURLToPath(import.meta.url));
const data = process.argv[2] ?? "data";
const osm = path.join(data, "osm");
const road = path.join(data, "road");
const next = path.join(data, "road.next");
const old = path.join(data, "road.old");

function step(script, ...args) {
  const started = Date.now();
  const run = spawnSync(process.execPath, [path.join(here, script), ...args], {
    stdio: "inherit",
  });
  if (run.status !== 0) {
    console.error(`${script} failed, and ${road} is unchanged`);
    process.exit(1);
  }
  console.log(`${script} took ${Math.round((Date.now() - started) / 1000)}s`);
}

step("fetch-road-data.mjs", osm);
fs.rmSync(next, { recursive: true, force: true });
step(
  "road-build.mjs",
  path.join(osm, "us-latest.osm.pbf"),
  path.join(osm, "outlines"),
  next,
);
step("check-road-data.mjs", next);
fs.rmSync(old, { recursive: true, force: true });
if (fs.existsSync(road)) fs.renameSync(road, old);
fs.renameSync(next, road);
fs.rmSync(old, { recursive: true, force: true });
console.log(`${road} rebuilt`);
