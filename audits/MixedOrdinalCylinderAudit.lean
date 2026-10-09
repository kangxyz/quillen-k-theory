import Quillen.Topology.Realization.MixedOrdinalRealization
import Lean.Util.CollectAxioms

open Lean in
run_cmd do
  let env ← getEnv
  let targets := #[`Quillen.Topology.Realization.MixedOrdinal,
    `Quillen.Topology.Realization.MixedOrdinalEndpoints,
    `Quillen.Topology.Realization.MixedOrdinalCylinder,
    `Quillen.Topology.Realization.MixedOrdinalFunctor,
    `Quillen.Topology.Realization.MixedOrdinalContraction,
    `Quillen.Topology.Realization.MixedOrdinalBisimplicial,
    `Quillen.Topology.Realization.MixedOrdinalRealization]
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let origin := env.header.moduleNames[index.toNat]!
    unless targets.contains origin do continue
    count := count + 1
    let axioms ← collectAxioms name
    for dependency in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{origin}: {name} depends on unsupported assumption {dependency}"
    logInfo m!"ACCEPTED {origin}: {name}: {axioms}"
  unless count == 183 do throwError "Expected 183 mixed cylinder origins, got {count}"
  logInfo m!"Audited all {count} mixed cylinder declaration origins."

noncomputable section
open CategoryTheory Opposite
open scoped Simplicial Topology
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Quillen.MixedOrdinalCylinder
example (n : SimplexCategory) (φ : Cut n) (i : Fin (n.len + 1)) :
    (firstIndex φ).toOrderHom i ≤ (switchedIndex φ).toOrderHom i := firstIndex_le_switchedIndex φ i
example {n m : SimplexCategory} (α : n ⟶ m) (φ : Cut m) :
    switchedIndex (α ≫ φ) ≫ mixedMap α (fun _ ↦ le_rfl) = α ≫ switchedIndex φ :=
  switchedIndex_naturality α φ
example (n : SimplexCategory) : mixedOrdinal (zeroCut n) ≅ n := zeroIso n
example (n : SimplexCategory) : mixedOrdinal (oneCut n) ≅ OrdinalSubdivision.δ.obj n := oneIso n
example (n : SimplexCategory) : (zeroIso n).inv = firstIndex (zeroCut n) := rfl
example (n : SimplexCategory) : (oneIso n).hom = inclusion (oneCut n) := rfl
example (n : SimplexCategory) (i j : Fin (n.len + 1)) :
    (firstIndex (oneCut n)).toOrderHom i ≤ (switchedIndex (oneCut n)).toOrderHom j :=
  firstIndex_one_le_switchedIndex n i j
example (X : SSet.{u}) : zeroSection X ≫ projection X = 𝟙 X := zeroSection_projection X
example (X : SSet.{u}) : oneSection X ≫ projection X = OrdinalSubdivision.endpoint X := oneSection_projection X
example (X : SSet.{u}) : SSet.Homotopy (projection X ≫ zeroSection X) (𝟙 _) := contraction X
example (X : SSet.{u}) : (projectionRealizationHomotopyEquiv X).toFun =
    (SSet.toTop.map (projection X)).hom := rfl
example (X : SSet.{u}) : (oneSectionRealizationHomotopyEquiv X).toFun =
    (SSet.toTop.map (oneSection X)).hom := rfl
example (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) (n m : SimplexCategoryᵒᵖ) :
    ((outerCylinder X).obj n).obj m =
      (Σ φ : Cut n.unop, (X.obj (op (mixedOrdinal φ))).obj m) := rfl
example (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) : outerZeroSection X ≫ outerProjection X = 𝟙 X :=
  outerZeroSection_projection X
example (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    outerOneSection X ≫ outerProjection X = OrdinalSubdivision.horizontalEndpoint X :=
  outerOneSection_projection X
example (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    SSet.Homotopy (TheoremA.diagonalMap (outerProjection X) ≫
      TheoremA.diagonalMap (outerZeroSection X)) (𝟙 _) := outerContraction X
example (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    (outerProjectionRealizationHomotopyEquiv X).toFun =
      (SSet.toTop.map (TheoremA.diagonalMap (outerProjection X))).hom := rfl
example (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    (outerOneSectionRealizationHomotopyEquiv X).toFun =
      (SSet.toTop.map (TheoremA.diagonalMap (outerOneSection X))).hom := rfl
end Quillen.MixedOrdinalCylinder
