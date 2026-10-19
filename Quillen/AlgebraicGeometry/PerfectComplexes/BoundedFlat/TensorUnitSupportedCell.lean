/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitSupportedRowPasting
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitSupportedCoefficientSpectrum
public import Quillen.Waldhausen.SConstruction.Iterated.RowTransformationInputNaturality
public import Quillen.Waldhausen.SConstruction.Iterated.RowTransformationRealization

/-! # Independent genuine tensor cells on the actual supported Model

First apply actual source evaluation to the input finite S-diagram, then the original tensor
coefficient cell. This construction precedes identification with any internal identity-unit cell.
Both cylinder directions and the genuine stage-zero tensor row remain explicit.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite MonoidalCategory
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.SupportedTensorEvaluation
open GlobalSectionChangeIndex
variable {A B : Scheme.OpenPairs.{u}} (p : A ⟶ B) (r : (Γ(A.obj.right, ⊤))ˣ)

/-- Evaluate the original finite input, retaining both independent tensor-cell cylinders. -/
def tensorCellCylinder (k : ℕ) :=
  (((stages k).map (evaluationModel (X := op B.obj.right) B.obj.hom) ▷ Δ[1]) ▷ Δ[1]) ≫
    tensorSupportedPairCoefficientStageCylinder p r k

/-- The initial cell is the independently built original tensor coefficient row. -/
theorem tensorCellCylinder_zero :
    tensorCellCylinder p r 0 =
      (((stages 0).map (evaluationModel (X := op B.obj.right) B.obj.hom) ▷ Δ[1]) ▷ Δ[1]) ≫
        tensorSupportedPairSmallCoefficientCylinder p r := by
  unfold tensorCellCylinder
  rw [tensorSupportedPairCoefficientStageCylinder_zero]

/-- The original full input-map law identifies every finite tensor cell before realization. -/
theorem tensorCellCylinder_eq (k : ℕ) :
    tensorCellCylinder p r k =
      rowTransformationCylinder
        (F := tensorModelMap p) (G := tensorModelMap p)
        (whiskerLeft (evaluationModel (X := op B.obj.right) B.obj.hom).functor
          (tensorSupportedPairModelTransformation p r))
        (fun A => tensorSupportedPairModelTransformation_weak p r
          ((evaluationModel (X := op B.obj.right) B.obj.hom).functor.obj A)) k :=
  (rowTransformationCylinder_precomp
    (tensorSupportedPairModelTransformation p r)
    (tensorSupportedPairModelTransformation_weak p r)
    (evaluationModel (X := op B.obj.right) B.obj.hom) k).symm

/-- Realization of the independent tensor cell, before the internal-unit comparison. -/
def tensorCellRealization (k : ℕ) :
    C(unitInterval ×
        (unitInterval × stageSpace k (supportedModel (X := op B.obj.right) B.obj.hom)),
      stageSpace (k + 1)
        (modelOf (boundedFlatPerfectSupportedWaldhausen A.obj.hom))) :=
  ⟨fun z => SSet.toTop.map (tensorCellCylinder p r k)
    ((Quillen.realizationCylinderIso
      ((stages k).obj (supportedModel (X := op B.obj.right) B.obj.hom) ⊗ Δ[1])).inv
      ((Quillen.realizationCylinderIso
        ((stages k).obj (supportedModel (X := op B.obj.right) B.obj.hom))).inv
        (z.2.2, ULift.up z.2.1), ULift.up z.1)), by fun_prop⟩

/-- The complete realized double cylinder is the genuine tensor Model transformation cell. -/
theorem tensorCellRealization_eq (k : ℕ) :
    tensorCellRealization p r k =
      rowTransformationRealization (tensorModelUnit p r) (tensorModelUnit_weak p r) k := by
  apply ContinuousMap.ext
  intro z
  change SSet.toTop.map (tensorCellCylinder p r k) _ = _
  rw [tensorCellCylinder_eq]
  rfl

/-- Every positive spectrum level retains both independent realized tensor-cell times. -/
theorem tensorCell_succ (k : ℕ) (t s : unitInterval)
    (x : stageSpace k (supportedModel (X := op B.obj.right) B.obj.hom)) :
    Path.toContinuousMap
      ((rowTransformationSpectrumHomotopy (tensorModelUnit p r)
        (tensorModelUnit_weak p r)).level (k + 1) (t, x)) s =
      tensorCellRealization p r k (s, (t, x)) := by
  rw [tensorCellRealization_eq]
  exact rowTransformationSpectrumHomotopy_succ _ _ k t s x

/-- Degree zero retains the additional original input-loop coordinate. -/
theorem tensorCell_zero (t a s : unitInterval)
    (γ : Path (stagePoint 0 (supportedModel (X := op B.obj.right) B.obj.hom))
      (stagePoint 0 (supportedModel (X := op B.obj.right) B.obj.hom))) :
    Path.toContinuousMap (Path.toContinuousMap
      ((rowTransformationSpectrumHomotopy (tensorModelUnit p r)
        (tensorModelUnit_weak p r)).level 0 (t, γ)) a) s =
      tensorCellRealization p r 0 (s, (t, γ a)) := by
  rw [tensorCellRealization_eq]
  exact rowTransformationSpectrumHomotopy_zero _ _ t a s γ

end Quillen.PerfectComplexes.SupportedTensorEvaluation
