/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitIteratedPrism

/-!
# The restricted tensor prism on original pullback grids

Every raw pullback S-grid is tensored with the original coefficient edge. The comparison with
the raw nerve cylinder retains all original entries and chain maps. The normalized iterated
construction has its literal quotient-row successor equation, rather than an assumed tower
compatibility. Together with the explicit normalization and structure formulas, this identifies
the restricted tensor-edge action at the original iterated-S levels.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS
open scoped Simplicial
universe u
namespace Quillen.PerfectComplexes

/-- On every raw geometric pullback grid, the original tensor-unit nerve cylinder is the
independently constructed actual coefficient tensor edge times the pulled-back input. -/
theorem boundedFlatPerfectTensorUnitPullbackPrism_original {X Y : Scheme.{u}} (f : X ⟶ Y)
    (r : (Γ(X, ⊤))ˣ) {n m : SimplexCategory} (A : Grid₂ n m ⥤ BoundedFlatPerfect Y)
    (τ : m ⟶ ⦋1⦌) :
    nerveCylinderDiagram
      (whiskerLeft A (boundedFlatPerfectTensorUnitPullbackAutomorphism f r).hom) τ ⋙
        (boundedFlatPerfect X).ι =
      complexTensorUnitPrism X r
        (A ⋙ boundedFlatPerfectPullback f ⋙ (boundedFlatPerfect X).ι) τ := by
  rw [← iteratedNerveCylinderDiagram_postcomp, complexTensorUnitPrism_eq_nerve]
  congr 1
  apply NatTrans.ext
  funext p
  change (boundedFlatPerfect X).ι.map
    ((boundedFlatPerfectTensorUnitAutomorphism X r).hom.app
      ((boundedFlatPerfectPullback f).obj (A.obj p))) = _
  exact boundedFlatPerfectTensorUnitAutomorphism_hom_original X r
    ((boundedFlatPerfectPullback f).obj (A.obj p))

/-- The independent tensor-edge construction preserves the actual quotient-grid conditions
after arbitrary geometric pullback, with no flatness assumption on the scheme map. -/
theorem boundedFlatPerfectTensorUnitPullbackPrism_isSimplex₂ {X Y : Scheme.{u}} (f : X ⟶ Y)
    (r : (Γ(X, ⊤))ˣ) {n m : SimplexCategory} (A : Grid₂ n m ⥤ BoundedFlatPerfect Y)
    (hA : IsSimplex₂ (boundedFlatPerfectWaldhausen Y).cof
      (boundedFlatPerfectWaldhausen Y).weq A) (τ : m ⟶ ⦋1⦌) :
    IsSimplex₂ (boundedFlatPerfectWaldhausen X).cof (boundedFlatPerfectWaldhausen X).weq
      (nerveCylinderDiagram
        (whiskerLeft A (boundedFlatPerfectTensorUnitPullbackAutomorphism f r).hom) τ) :=
  nerveCylinderDiagram_isSimplex₂ (boundedFlatPerfectWaldhausen X) _
    (fun _ ↦ (boundedFlatPerfectWaldhausen X).weq_iso _ inferInstance)
    (hA.postcomp _ _ (boundedFlatPerfectTensorUnitPullback_exact f))
    (hA.postcomp _ _ (boundedFlatPerfectTensorUnitPullback_exact f)) τ

/-- The normalized iterated tensor prism is prolonged by the actual quotient-row action at
each successor, with no separately chosen higher compatibility. -/
theorem tensorUnitPullback_prism_succ {X Y : Scheme.{u}} (f : X ⟶ Y)
    (r : (Γ(X, ⊤))ˣ) (k : ℕ) (n : SimplexCategoryᵒᵖ)
    (A : ((stages (k + 1)).obj (modelOf (boundedFlatPerfectWaldhausen Y))).obj n)
    (τ : (Δ[1]).obj n) :
    stageTransformationFunction (k + 1) (tensorUnitPullbackModelTransformation f r)
      (tensorUnitPullbackModelTransformation_weak f r) n A τ =
    stageTransformationFunction k (rowsTransformation (tensorUnitPullbackModelTransformation f r)
      n.unop) (rowsTransformation_weak (tensorUnitPullbackModelTransformation f r)
        (tensorUnitPullbackModelTransformation_weak f r) n.unop) n A τ := rfl

end Quillen.PerfectComplexes
