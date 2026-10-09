import Consumer
import Lean.Util.CollectAxioms
/-! Independently audit the downstream declarations as well as compiling them. -/
open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let consumerModule := match env.getModuleIdxFor? name with
      | some index => (`Consumer).isPrefixOf env.header.moduleNames[index.toNat]!
      | none => false
    if consumerModule then
      count := count + 1
      for dependency in ← collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
          throwError "{name} depends on unsupported assumption {dependency}"
  logInfo m!"Audited {count} downstream declarations: only standard Lean logical foundations."
