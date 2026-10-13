/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.CategoryTheory.TheoremB.SkeletalWeakCartesianInduction
public import Quillen.CategoryTheory.TheoremB.ReplacementStageOne
public import Quillen.Topology.Realization.Cartesian.CoproductAssembly

/-!
# Weak comparison at an actual replacement vertex

The first skeletal stage is the genuine coproduct of diagram values. Its
component square is homotopy cartesian for arbitrary coefficient maps. Pasting
with the weak stage-to-total theorem gives the original vertex comparison,
retaining the realized inclusion, coefficient map, and entire constant path.
-/
@[expose] public section

noncomputable section
open CategoryTheory Limits Opposite
open scoped Simplicial Topology unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Quillen.CartesianRealization.Skeletal
open TheoremA
variable {D : Type u} [SmallCategory D] {H J : D ⥤ SSet.{u}} (η : H ⟶ J)

/-- Include a diagram value into the actual first skeletal stage. -/
def replacementStageOneVertexMap (H : D ⥤ SSet.{u}) (d : D) :
    C(|H.obj d|, (realizedReplacementSkeleton H).obj 1) :=
  (realizedReplacementStageOneHomeomorph H :
    C((Σ i, |H.obj i|), (realizedReplacementSkeleton H).obj 1)).comp
      (ContinuousMap.sigmaMk (X := fun i ↦ |H.obj i|) d)

/-- Coefficient naturality at the actual stage-one vertex. -/
theorem replacementStageOneVertex_square (d : D) :
    ((realizedReplacementSkeletonMap η).app 1).hom.comp (replacementStageOneVertexMap H d) =
      (replacementStageOneVertexMap J d).comp (SSet.toTop.map (η.app d)).hom := by
  apply ContinuousMap.ext
  intro x
  exact realizedReplacementStageOneHomeomorph_naturality η d x

/-- Coproduct components are genuinely cartesian, without a transition assumption. -/
theorem replacementStageOneVertex_cartesian (d : D) :
    Cartesian (SSet.toTop.map (η.app d)).hom ((realizedReplacementSkeletonMap η).app 1).hom
      (replacementStageOneVertexMap H d) (replacementStageOneVertexMap J d)
      (replacementStageOneVertex_square η d) := by
  apply cartesianOfCoordinates _ _ _ _ _
    (SSet.toTop.map (η.app d)).hom (sigmaMap (fun i ↦ (SSet.toTop.map (η.app i)).hom))
    (ContinuousMap.sigmaMk (X := fun i ↦ |H.obj i|) d)
    (ContinuousMap.sigmaMk (X := fun i ↦ |J.obj i|) d) rfl
    (Homeomorph.refl _) (realizedReplacementStageOneHomeomorph H).symm
    (Homeomorph.refl _) (realizedReplacementStageOneHomeomorph J).symm
  · rfl
  · apply ContinuousMap.ext
    intro z
    obtain ⟨⟨i,x⟩,rfl⟩ := (realizedReplacementStageOneHomeomorph H).surjective z
    change sigmaMap (fun i ↦ (SSet.toTop.map (η.app i)).hom)
      ((realizedReplacementStageOneHomeomorph H).symm
      (realizedReplacementStageOneHomeomorph H ⟨i,x⟩)) =
      (realizedReplacementStageOneHomeomorph J).symm
        ((realizedReplacementSkeletonMap η).app 1
          (realizedReplacementStageOneHomeomorph H ⟨i,x⟩))
    rw [Homeomorph.symm_apply_apply, realizedReplacementStageOneHomeomorph_naturality,
      Homeomorph.symm_apply_apply]
    rfl
  · apply ContinuousMap.ext
    intro x
    exact ((realizedReplacementStageOneHomeomorph H).symm_apply_apply ⟨d,x⟩).symm
  · apply ContinuousMap.ext
    intro x
    exact ((realizedReplacementStageOneHomeomorph J).symm_apply_apply ⟨d,x⟩).symm
  · exact cartesianComponentInclusion (fun i ↦ (SSet.toTop.map (η.app i)).hom) d

/-- The original replacement vertex square commutes strictly. -/
theorem replacementVertex_square (d : D) :
    (SSet.toTop.map (diagonalMap (simplicialReplacementMap η))).hom.comp
      (SSet.toTop.map (replacementVertexInclusion H d)).hom =
    (SSet.toTop.map (replacementVertexInclusion J d)).hom.comp
      (SSet.toTop.map (η.app d)).hom := by
  change (SSet.toTop.map (replacementVertexInclusion H d) ≫
      SSet.toTop.map (diagonalMap (simplicialReplacementMap η))).hom =
    (SSet.toTop.map (η.app d) ≫ SSet.toTop.map (replacementVertexInclusion J d)).hom
  rw [← Functor.map_comp, ← Functor.map_comp]
  rfl

/-- Weak transition comparisons imply complete weakness of the actual vertex comparison. -/
theorem replacementVertexComparison_isWeakHomotopyEquivalence
    (htrans : TransitionWeakCartesian η) (d : D) :
    IsWeakHomotopyEquivalence (HomotopyPullback.comparison
      (SSet.toTop.map (diagonalMap (simplicialReplacementMap η))).hom
      (SSet.toTop.map (replacementVertexInclusion J d)).hom
      (SSet.toTop.map (η.app d)).hom
      (SSet.toTop.map (replacementVertexInclusion H d)).hom
      (replacementVertex_square η d)) := by
  have h := (replacementStageOneVertex_cartesian η d).weak.paste
    (replacementSkeletonComparison_isWeakHomotopyEquivalence η htrans 1)
  apply h.congr rfl
    (congrArg TopCat.Hom.hom (realizedReplacementSkeleton_colimitMap η))
  · apply ContinuousMap.ext
    intro x
    exact realizedReplacementStageOneHomeomorph_colimit H d x
  · apply ContinuousMap.ext
    intro x
    exact realizedReplacementStageOneHomeomorph_colimit J d x

end Quillen.CartesianRealization.Skeletal
