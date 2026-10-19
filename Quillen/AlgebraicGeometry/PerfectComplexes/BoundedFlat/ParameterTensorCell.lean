/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterTensorRowPasting
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitCoefficientStages
public import Quillen.Waldhausen.SConstruction.Iterated.RowTransformationInputNaturality
public import Quillen.Waldhausen.SConstruction.Iterated.RowTransformationRealization

/-! # Independent genuine tensor cells on the literal parameter ambient Model

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
namespace Quillen.PerfectComplexes.ParameterTensorEvaluationRow
open GlobalSectionChangeIndex

/-- Evaluate the original finite input, retaining both independent tensor-cell cylinders. -/
def tensorCellCylinder (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) (k : ℕ) :=
  (((stages k).map (evaluationModel (op (scheme Q X))) ▷ Δ[1]) ▷ Δ[1]) ≫
    tensorUnitPullbackCoefficientStageCylinder (coefficientMap Q X)
      (ParameterLaurentUnit.projectedLaurentScalar Q X) k

/-- The initial cell is the independently built original tensor coefficient row. -/
theorem tensorCellCylinder_zero (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :
    tensorCellCylinder Q X 0 =
      (((stages 0).map (evaluationModel (op (scheme Q X))) ▷ Δ[1]) ▷ Δ[1]) ≫
        tensorUnitPullbackSmallCoefficientCylinder (coefficientMap Q X)
          (ParameterLaurentUnit.projectedLaurentScalar Q X) := by
  unfold tensorCellCylinder
  rw [tensorUnitPullbackCoefficientStageCylinder_zero]

/-- The original full input-map law identifies every finite tensor cell before realization. -/
theorem tensorCellCylinder_eq (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) (k : ℕ) :
    tensorCellCylinder Q X k =
      rowTransformationCylinder
        (F := tensorModelMap Q X) (G := tensorModelMap Q X)
        (whiskerLeft (evaluationModel (op (scheme Q X))).functor
          (tensorUnitPullbackModelTransformation (coefficientMap Q X)
            (ParameterLaurentUnit.projectedLaurentScalar Q X)))
        (fun A => tensorUnitPullbackModelTransformation_weak (coefficientMap Q X)
          (ParameterLaurentUnit.projectedLaurentScalar Q X)
          ((evaluationModel (op (scheme Q X))).functor.obj A)) k :=
  (rowTransformationCylinder_precomp
    (tensorUnitPullbackModelTransformation (coefficientMap Q X)
      (ParameterLaurentUnit.projectedLaurentScalar Q X))
    (tensorUnitPullbackModelTransformation_weak (coefficientMap Q X)
      (ParameterLaurentUnit.projectedLaurentScalar Q X))
    (evaluationModel (op (scheme Q X))) k).symm

/-- Realization of the independent tensor cell, before the internal-unit comparison. -/
def tensorCellRealization (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) (k : ℕ) :
    C(unitInterval × (unitInterval × stageSpace k ((ParameterModels.ambient Q).obj X)),
      stageSpace (k + 1)
        (modelOf (boundedFlatPerfectWaldhausen (scheme Q (laurent.op.obj X))))) :=
  ⟨fun z => SSet.toTop.map (tensorCellCylinder Q X k)
    ((Quillen.realizationCylinderIso
      ((stages k).obj ((ParameterModels.ambient Q).obj X) ⊗ Δ[1])).inv
      ((Quillen.realizationCylinderIso ((stages k).obj ((ParameterModels.ambient Q).obj X))).inv
        (z.2.2, ULift.up z.2.1), ULift.up z.1)), by fun_prop⟩

/-- The complete realized double cylinder is the genuine tensor Model transformation cell. -/
theorem tensorCellRealization_eq (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) (k : ℕ) :
    tensorCellRealization Q X k =
      rowTransformationRealization (tensorModelUnit Q X) (tensorModelUnit_weak Q X) k := by
  apply ContinuousMap.ext
  intro z
  change SSet.toTop.map (tensorCellCylinder Q X k) _ = _
  rw [tensorCellCylinder_eq]
  rfl

/-- Every positive spectrum level retains both independent realized tensor-cell times. -/
theorem tensorCell_succ (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) (k : ℕ) (t s : unitInterval)
    (x : stageSpace k ((ParameterModels.ambient Q).obj X)) :
    Path.toContinuousMap
      ((rowTransformationSpectrumHomotopy (tensorModelUnit Q X)
        (tensorModelUnit_weak Q X)).level (k + 1) (t, x)) s =
      tensorCellRealization Q X k (s, (t, x)) := by
  rw [tensorCellRealization_eq]
  exact rowTransformationSpectrumHomotopy_succ _ _ k t s x

/-- Degree zero retains the additional original input-loop coordinate. -/
theorem tensorCell_zero (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) (t a s : unitInterval)
    (γ : Path (stagePoint 0 ((ParameterModels.ambient Q).obj X))
      (stagePoint 0 ((ParameterModels.ambient Q).obj X))) :
    Path.toContinuousMap (Path.toContinuousMap
      ((rowTransformationSpectrumHomotopy (tensorModelUnit Q X)
        (tensorModelUnit_weak Q X)).level 0 (t, γ)) a) s =
      tensorCellRealization Q X 0 (s, (t, γ a)) := by
  rw [tensorCellRealization_eq]
  exact rowTransformationSpectrumHomotopy_zero _ _ t a s γ

end Quillen.PerfectComplexes.ParameterTensorEvaluationRow
