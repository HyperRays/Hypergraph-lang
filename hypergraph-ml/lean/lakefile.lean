import Lake
open Lake DSL

package HypergraphFFI where
  packagesDir := "../../ACUIhE/.lake/packages"

require ACUIhE from "../../ACUIhE"

lean_lib HypergraphFFI

lean_lib HMEmbedding

/-- Bundle precisely the API module's native import closure. The Lean runtime
    remains a shared dependency from the pinned toolchain. -/
target acuihe_native pkg : System.FilePath := do
  let some root := (← getWorkspace).findModule? `HypergraphFFI
    | error "HypergraphFFI module not found"
  let infoJob ← root.linkInfoExport.fetch
  infoJob.bindM fun info => do
    unless info.libs.isEmpty do
      error "ACUIhE added native shared dependencies; update the OCaml linker configuration"
    buildStaticLib (pkg.buildDir / "lib" / "libacuihe_native.a")
      (info.objs.map Job.pure)

/-- OCaml's bytecode loader uses its conventional dll*.so name, including
    on macOS. Native executables link the static archive above. -/
target acuihe_shared pkg : Dynlib := do
  let some root := (← getWorkspace).findModule? `HypergraphFFI
    | error "HypergraphFFI module not found"
  let infoJob ← root.linkInfoExport.fetch
  infoJob.mapM fun info => do
    let runtime := (← getLeanInstall).leanLibDir
    let args := info.args.push s!"-Wl,-rpath,{runtime}"
    addPureTrace args "acuihe-native-link-args"
    buildLeanSharedLibSync "acuihe_native"
      (pkg.buildDir / "lib" / "dllacuihe_native.so")
      info.objs info.libs args (linkDeps := true)
