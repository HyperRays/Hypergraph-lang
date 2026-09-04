// One program through one output, for comparing a browser build against the
// native binary.
//
//   node web/render.mjs BUILD FILE report|incidence|facts
import { readFileSync } from "node:fs";
import { load } from "./load.mjs";

const [build, file, mode] = process.argv.slice(2);
const hg = await load(build);
const src = readFileSync(file, "utf8");
process.stdout.write(
  mode === "report" ? hg.report(src)
    : mode === "incidence" ? hg.incidence(src)
      : hg.facts(src, ""));
