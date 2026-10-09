import Quillen.Scheme.OpenImmersionFunctor
import Lean.Util.CollectAxioms
-- Audit every declaration of both new source modules, including private helpers.
open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let sourceModule := match env.getModuleIdxFor? name with
      | some index => #[`Quillen.Scheme.RestrictionFunctoriality, `Quillen.Scheme.OpenImmersionFunctor].contains
          env.header.moduleNames[index.toNat]!
      | none => false
    if sourceModule then
      count := count + 1
      for dependency in ← collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
          throwError "{name} depends on unsupported assumption {dependency}"
  logInfo m!"Audited {count} scheme-restriction declarations: only standard Lean logical foundations."
