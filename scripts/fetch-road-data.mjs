// Downloads what the road build needs from Geofabrik: an OpenStreetMap extract
// and the outline of each state. Files already there are skipped, and everything
// lands in the gitignored data folder.
//
//   node scripts/fetch-road-data.mjs [folder] [extract]
//
// The extract defaults to the whole US. A smaller one, such as
// north-america/us/delaware, is enough to try the build.
import fs from "node:fs";
import path from "node:path";
import { Readable } from "node:stream";
import { pipeline } from "node:stream/promises";

const SOURCE = "https://download.geofabrik.de";

// The lower 48 and DC. Alaska and Hawaii have no contractors.
const STATES = [
  "alabama",
  "arizona",
  "arkansas",
  "california",
  "colorado",
  "connecticut",
  "delaware",
  "district-of-columbia",
  "florida",
  "georgia",
  "idaho",
  "illinois",
  "indiana",
  "iowa",
  "kansas",
  "kentucky",
  "louisiana",
  "maine",
  "maryland",
  "massachusetts",
  "michigan",
  "minnesota",
  "mississippi",
  "missouri",
  "montana",
  "nebraska",
  "nevada",
  "new-hampshire",
  "new-jersey",
  "new-mexico",
  "new-york",
  "north-carolina",
  "north-dakota",
  "ohio",
  "oklahoma",
  "oregon",
  "pennsylvania",
  "rhode-island",
  "south-carolina",
  "south-dakota",
  "tennessee",
  "texas",
  "utah",
  "vermont",
  "virginia",
  "washington",
  "west-virginia",
  "wisconsin",
  "wyoming",
];

// Written under a temporary name, so an interrupted download is never skipped
// as finished on the next run.
async function download(url, file) {
  if (fs.existsSync(file)) return;
  const response = await fetch(url);
  if (!response.ok || response.body === null) {
    throw new Error(`${url}: ${response.status}`);
  }
  const partial = `${file}.partial`;
  await pipeline(
    Readable.fromWeb(response.body),
    fs.createWriteStream(partial),
  );
  fs.renameSync(partial, file);
}

const [folder = "data/osm", extract = "north-america/us"] =
  process.argv.slice(2);
const outlines = path.join(folder, "outlines");
fs.mkdirSync(outlines, { recursive: true });

for (const state of STATES) {
  await download(
    `${SOURCE}/north-america/us/${state}.poly`,
    path.join(outlines, `${state}.poly`),
  );
}

const name = `${path.basename(extract)}-latest.osm.pbf`;
await download(`${SOURCE}/${extract}-latest.osm.pbf`, path.join(folder, name));
console.log(`${path.join(folder, name)} and ${STATES.length} outlines ready`);
