import Lean.Util.CollectAxioms
import Quillen.Topology.Realization.ProductComparison

open Lean in
run_cmd do
  let env ← getEnv
  let wanted : Array Name := #[`Quillen.Topology.Realization.FiniteCompact,
    `Quillen.Topology.Realization.FiniteSkeleton, `Quillen.Topology.Realization.FiniteHausdorff,
    `Quillen.Topology.Realization.ProductSupport, `Quillen.Topology.Realization.ProductComparison,
    `Quillen.Topology.HomotopyGroups.CompactLifting, `Quillen.Topology.HomotopyGroups.Product]
  let mut count : Nat := 0
  let mut seen : NameSet := {}
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let origin := env.header.moduleNames[index.toNat]!
    unless wanted.contains origin do continue
    seen := seen.insert origin
    count := count + 1
    for dependency in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
    logInfo m!"ACCEPTED {name}"
  unless count == 46 do throwError "Expected frozen count46, found {count}"
  unless seen.size == 7 do throwError "Missing defining module"
  logInfo m!"Audited all {count} origins of the seven actual product-topology modules."

noncomputable section
open CategoryTheory MonoidalCategory Quillen Quillen.ProductRealization
open scoped Simplicial Topology
universe u

example (X : SSet.{u}) [X.Finite] : CompactSpace |X| := inferInstance
example (X : SSet.{u}) [X.Finite] : T2Space |X| := inferInstance
example (X : SSet.{u}) [X.Finite] : LocallyCompactSpace |X| := inferInstance
example (X Y : SSet.{u}) : Function.Injective (comparison X Y) := comparison_injective X Y
example (X Y : SSet.{u}) : HasCompactSourceLifts (comparison X Y) := comparison_compact_lifts X Y
example (X Y : SSet.{u}) (p : |X ⊗ Y|) (n : ℕ) :
    (comparisonPiEquiv X Y p n).toMonoidHom = piMap n (comparison X Y) rfl := rfl
example (X Y : SSet.{u}) (p : |X ⊗ Y|) :
    Function.Bijective (homotopyGroupMap (N := Fin 0) (comparison X Y) (x := p) rfl) :=
  homotopyGroupMap_bijective_of_compact_lifts _ (comparison_injective X Y)
    (comparison_compact_lifts X Y) p 0
example (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y] (x : X) (y : Y) :
    (piProdEquiv 0 x y).toMonoidHom =
      (piMap 0 ContinuousMap.fst rfl).prod (piMap 0 ContinuousMap.snd rfl) := rfl
