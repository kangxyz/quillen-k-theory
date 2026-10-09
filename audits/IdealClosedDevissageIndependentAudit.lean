import Quillen.Devissage.FiltrationRefinement
import Quillen.Devissage.FiniteCentralFamily
import Quillen.Devissage.FiltrationFunctor
import Quillen.GTheory.FiniteModules.IdealClosedSupport
import Quillen.GTheory.FiniteModules.IdealPowerFiltration
import Quillen.Scheme.Coherent.ClosedImmersion.IdealPushforward
import Quillen.Scheme.Coherent.ClosedImmersion.IdealSupport
import Quillen.Scheme.Coherent.ClosedImmersion.IdealSupportDevissage
import Quillen.Scheme.Coherent.ClosedImmersion.IdealDevissage
import Quillen.Scheme.Coherent.ClosedImmersion.IdealLocalization
import Quillen.Scheme.Coherent.ClosedImmersion.IdealPowerFiltration
import Lean.Util.CollectAxioms
/-! Independent exact-source-module dependency audit, including private and generated declarations. -/
open Lean in
run_cmd do
  let env ← getEnv
  let modules := #[
    `Quillen.Devissage.FiltrationRefinement,
    `Quillen.Devissage.FiniteCentralFamily,
    `Quillen.Devissage.FiltrationFunctor,
    `Quillen.GTheory.FiniteModules.IdealClosedSupport,
    `Quillen.GTheory.FiniteModules.IdealPowerFiltration,
    `Quillen.Scheme.Coherent.ClosedImmersion.IdealPushforward,
    `Quillen.Scheme.Coherent.ClosedImmersion.IdealSupport,
    `Quillen.Scheme.Coherent.ClosedImmersion.IdealSupportDevissage,
    `Quillen.Scheme.Coherent.ClosedImmersion.IdealDevissage,
    `Quillen.Scheme.Coherent.ClosedImmersion.IdealLocalization,
    `Quillen.Scheme.Coherent.ClosedImmersion.IdealPowerFiltration]
  let mut total : Nat := 0
  let mut counts : NameMap Nat := {}
  for (name, _) in env.constants.toList do
    let source := match env.getModuleIdxFor? name with
      | some index => env.header.moduleNames[index.toNat]!
      | none => Name.anonymous
    if modules.contains source then
      total := total + 1
      counts := counts.insert source ((counts.find? source).getD 0 + 1)
      let dependencies ← collectAxioms name
      for dependency in dependencies do
        unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
          throwError "{name} depends on unsupported assumption {dependency}"
      logInfo m!"CHECKED {name}: {dependencies}"
  for source in modules do
    let count := (counts.find? source).getD 0
    if count == 0 then throwError "No declarations audited in required source module {source}"
    logInfo m!"MODULE {source}: {count} declarations"
  logInfo m!"PASS: {total} declarations in {modules.size} exact source modules; only propext, Classical.choice, Quot.sound."

#check @Quillen.CoherentScheme.ClosedImmersion.Ideal.coherentSupportedAway_iff_pow_le_annihilator
#check @Quillen.CoherentScheme.ClosedImmersion.Ideal.coherentIdealPowerFiltration
#check @Quillen.CoherentScheme.ClosedImmersion.Ideal.closedSupportGEquiv_pushforward
#check @Quillen.CoherentScheme.ClosedImmersion.Ideal.closedSupportedGEquiv_pushforward
#check @Quillen.CoherentScheme.ClosedImmersion.Ideal.affine_closed_open_longExact
#check @Quillen.CoherentScheme.ClosedImmersion.Ideal.affine_closed_open_GZero_tail
