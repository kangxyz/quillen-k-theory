import Quillen.Scheme.Coherent.ClosedImmersion.GeneralLocalization
import Quillen.Scheme.Coherent.ClosedImmersion.GeneralAnnihilator
import Quillen.Scheme.Coherent.ClosedImmersion.AffineIdealKernel
import Quillen.Scheme.Coherent.ClosedImmersion.IdealLocalization
import Lean.Util.CollectAxioms
/-! Independent exact-source-module dependency audit, including private and generated declarations. -/
open Lean in
run_cmd do
  let env ← getEnv
  let modules := #[
    `Quillen.Devissage.FiltrationRefinement,
    `Quillen.Devissage.FiniteCentralFamily,
    `Quillen.Devissage.FiltrationFunctor,
    `Quillen.Devissage.FiltrationSubcategory,
    `Quillen.Devissage.ReflectorFiltration,
    `Quillen.Devissage.KernelIteration,
    `Quillen.GTheory.FiniteModules.IdealClosedSupport,
    `Quillen.GTheory.FiniteModules.IdealPowerFiltration,
    `Quillen.Scheme.Coherent.ClosedImmersion.IdealPushforward,
    `Quillen.Scheme.Coherent.ClosedImmersion.IdealSupport,
    `Quillen.Scheme.Coherent.ClosedImmersion.IdealSupportDevissage,
    `Quillen.Scheme.Coherent.ClosedImmersion.IdealDevissage,
    `Quillen.Scheme.Coherent.ClosedImmersion.IdealLocalization,
    `Quillen.Scheme.Coherent.ClosedImmersion.IdealPowerFiltration,
    `Quillen.Scheme.Coherent.ClosedImmersion.AffinePullback,
    `Quillen.Scheme.Coherent.ClosedImmersion.GeneralPushforward,
    `Quillen.Scheme.Coherent.ClosedImmersion.GeneralPullback,
    `Quillen.Scheme.Coherent.ClosedImmersion.GeneralUnitBaseChange,
    `Quillen.Scheme.Coherent.ClosedImmersion.AffineReflection,
    `Quillen.Scheme.Coherent.ClosedImmersion.GeneralReflection,
    `Quillen.Scheme.Coherent.ClosedImmersion.AffineKernel,
    `Quillen.Scheme.Coherent.ClosedImmersion.AffineIdealKernel,
    `Quillen.Scheme.Coherent.ClosedImmersion.GeneralSupport,
    `Quillen.Scheme.Coherent.ClosedImmersion.GeneralNilpotence,
    `Quillen.Scheme.Coherent.ClosedImmersion.GeneralAnnihilator,
    `Quillen.Scheme.Coherent.ClosedImmersion.GeneralSupportDevissage,
    `Quillen.Scheme.Coherent.ClosedImmersion.GeneralDevissage,
    `Quillen.Scheme.Coherent.ClosedImmersion.GeneralLocalization,
    `Quillen.Scheme.Coherent.ClosedImmersion.NoetherianSource]
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
