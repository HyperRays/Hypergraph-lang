// Load either build and hand back the exported object.
//
// The two backends publish differently: js_of_ocaml's Js.export writes to
// module.exports under node, while the wasm loader sets a global and does so
// ASYNCHRONOUSLY, since it has a module to instantiate first. Callers should
// not have to know which, so this waits for whichever appears.
import { createRequire } from "node:module";
import { dirname, resolve } from "node:path";

export async function load(file) {
  const require = createRequire(resolve(file));
  // The wasm loader resolves its assets against require.main.filename.
  process.mainModule = { filename: resolve(file) };
  require.main = { filename: resolve(file) };
  const m = require(resolve(file));
  if (m && m.hypergraph) return m.hypergraph;
  for (let i = 0; i < 400 && !globalThis.hypergraph; i++)
    await new Promise((r) => setTimeout(r, 10));
  if (!globalThis.hypergraph) throw new Error(`no export from ${file}`);
  return globalThis.hypergraph;
}
