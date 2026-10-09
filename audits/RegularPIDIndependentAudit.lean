import Quillen.Scheme.Regular.SmallComparison
import Lean.Util.CollectAxioms
/-! Independent exact-source-module dependency audit, including private and generated declarations. -/
open Lean in
run_cmd do
  let env ← getEnv
  let modules := #[
    `Quillen.Resolution.Finite,
    `Quillen.Resolution.Closure,
    `Quillen.Resolution.QCalculus,
    `Quillen.Resolution.Covers,
    `Quillen.Resolution.FullQ,
    `Quillen.Resolution.InheritedQ,
    `Quillen.Resolution.LengthOne,
    `Quillen.Resolution.Transport,
    `Quillen.Scheme.Regular.Field,
    `Quillen.Scheme.Regular.FiniteProjectiveResolution,
    `Quillen.Scheme.Regular.AffineProjective,
    `Quillen.Scheme.Regular.AffineResolution,
    `Quillen.Scheme.Regular.SmallComparison]
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

#check @Quillen.Scheme.KToG_pid_bijective
#check @Quillen.Scheme.KToGPIDEquiv
#check @Quillen.SchemeSheaf.schemeKToG_bijective_of_length_one
#check @Quillen.Resolution.inclusionKMap_bijective_of_length_one

universe u
example (R : CommRingCat.{u}) [IsDomain R] [IsPrincipalIdealRing R] (n : ℕ) :
    (Quillen.Scheme.KToGPIDEquiv R n).toMonoidHom =
      Quillen.Scheme.KToG (AlgebraicGeometry.Spec R) n := rfl

example (R : CommRingCat.{u}) [IsDomain R] [IsPrincipalIdealRing R] (n : ℕ) :
    Function.Bijective (Quillen.Scheme.KToG (AlgebraicGeometry.Spec R) n) :=
  Quillen.Scheme.KToG_pid_bijective R n
