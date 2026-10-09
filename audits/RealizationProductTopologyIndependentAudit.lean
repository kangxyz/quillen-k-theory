import Quillen.Topology.Realization.ProductComparison
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let targets := #[`Quillen.Topology.Realization.FiniteCompact,
    `Quillen.Topology.Realization.FiniteSkeleton,
    `Quillen.Topology.Realization.FiniteHausdorff,
    `Quillen.Topology.Realization.ProductSupport,
    `Quillen.Topology.Realization.ProductComparison,
    `Quillen.Topology.HomotopyGroups.CompactLifting,
    `Quillen.Topology.HomotopyGroups.Product]
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let origin := env.header.moduleNames[index.toNat]!
    unless targets.contains origin do continue
    count := count + 1
    let axioms ← collectAxioms name
    for dependency in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
    logInfo m!"ACCEPTED {origin}: {name}: {axioms}"
  unless count == 46 do throwError "Expected 46 realization-product topology origins, got {count}"
  logInfo m!"Audited all {count} realization-product topology origins."

noncomputable section
open CategoryTheory MonoidalCategory CartesianMonoidalCategory Quillen
open scoped Simplicial Topology
universe u v
-- Finite realizations use their unchanged actual topology.
example (X : SSet.{u}) [X.Finite] : CompactSpace |X| ∧ T2Space |X| ∧
    LocallyCompactSpace |X| := ⟨inferInstance, inferInstance, inferInstance⟩
-- No finite factor is required for injectivity or actual compact lifting.
example (X Y : SSet.{u}) : Function.Injective (ProductRealization.comparison X Y) :=
  ProductRealization.comparison_injective X Y
example (X Y : SSet.{u}) : HasCompactSourceLifts (ProductRealization.comparison X Y) :=
  ProductRealization.comparison_compact_lifts X Y
-- The comparison equivalence retains precisely the original based forward map.
example (X Y : SSet.{u}) (p : |X ⊗ Y|) (n : ℕ) :
    (ProductRealization.comparisonPiEquiv X Y p n).toMonoidHom =
      piMap n (prodComparison SSet.toTop X Y).hom rfl := rfl
-- Dimension zero is included at the underlying homotopy-set level.
example {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (e : C(X,Y)) (he : Function.Injective e) (hl : HasCompactSourceLifts e) (x : X) :
    Function.Bijective (homotopyGroupMap (N := Fin 0) e (x := x) rfl) :=
  homotopyGroupMap_bijective_of_compact_lifts e he hl x 0
-- In particular the fundamental group needs no commutativity assumption.
example {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (x : X) (y : Y) : (piProdEquiv 0 x y).toMonoidHom =
      (piMap 0 ContinuousMap.fst rfl).prod (piMap 0 ContinuousMap.snd rfl) := rfl
