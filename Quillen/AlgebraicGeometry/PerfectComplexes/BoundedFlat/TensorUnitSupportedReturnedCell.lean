/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitSupportedReturnedModel
public import Quillen.Topology.Prespectrum.RelativeHomotopyLevels
public import Quillen.Waldhausen.SConstruction.Iterated.RowTransformationSpectrumNaturality

/-! # The genuine supported tensor first-row cell in its original section target

All first-S row coordinates, forward multiplication times and zero-level input loops remain
in the actual row realization. The moving endpoint is the specified evaluation unit/unitor.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS Quillen.FunctorIdentityAutomorphism
open Quillen.LoopPrespectrum
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.SupportedTensorEvaluation
open GlobalSectionChangeIndex
variable {A B : Scheme.OpenPairs.{u}} (p : A ⟶ B) (r : (Γ(A.obj.right, ⊤))ˣ)

/-- The unchanged internal supported unit in its own section Model. -/
def sectionUnit :=
  (onFunctor (supportedPairModelMap p).functor
    (unit (X := op A.obj.right) A.obj.hom r)).hom

/-- The original supported internal row cell. -/
def sectionCell :=
  rowTransformationSpectrumHomotopy (F := supportedPairModelMap p)
    (G := supportedPairModelMap p) (sectionUnit p r)
    (fun _ => (supportedModel (X := op A.obj.right) A.obj.hom).waldhausen.weq_iso _
      (by dsimp [sectionUnit]; infer_instance))

/-- Independently realize the genuine tensor after the exact supported evaluation inverse. -/
def returnedTensorCell :=
  rowTransformationSpectrumHomotopy (F := returnedTensorModel p)
    (G := returnedTensorModel p) (returnedTensorUnit p r) (returnedTensorUnit_weak p r)

/-- The original categorical unit and tensor comparison provide this endpoint movement. -/
def returnedMovement :=
  rowTransformationSpectrumHomotopy (F := supportedPairModelMap p)
    (G := returnedTensorModel p) (returnedTensorIso p).hom
    (fun _ => (supportedModel (X := op A.obj.right) A.obj.hom).waldhausen.weq_iso _
      inferInstance)

/-- The supported first-row prism retains its complete moving endpoints. -/
def returnedPasting :
    ((sectionCell p r).trans (returnedMovement p)).RelHomotopy
      ((returnedMovement p).trans (returnedTensorCell p r)) := by
  let J := rowTransformationPasting
    (F := supportedPairModelMap p) (G := supportedPairModelMap p)
    (G' := returnedTensorModel p) (H := returnedTensorModel p)
    (sectionUnit p r) (returnedTensorIso p).hom (returnedTensorIso p).hom
    (returnedTensorUnit p r)
    (fun _ => (supportedModel (X := op A.obj.right) A.obj.hom).waldhausen.weq_iso _
      (by dsimp [sectionUnit]; infer_instance))
    (fun _ => (supportedModel (X := op A.obj.right) A.obj.hom).waldhausen.weq_iso _
      inferInstance)
    (fun _ => (supportedModel (X := op A.obj.right) A.obj.hom).waldhausen.weq_iso _
      inferInstance)
    (returnedTensorUnit_weak p r) (returnedTensorIso_unit p r)
  refine J.ofLevels _ _ ?_ ?_
  · intro n
    rw [Homotopy.postcomp_trans]
    apply Homotopy.trans_level_congr <;> rfl
  · intro n
    rw [Homotopy.postcomp_trans]
    apply Homotopy.trans_level_congr <;> rfl

/-- Every original time slice is the raw tensor row cell followed by the actual inverse. -/
theorem returnedTensorCell_at (t : unitInterval) :
    (returnedTensorCell p r).at t =
      (rowTransformationSpectrumHomotopy (tensorModelUnit p r)
        (tensorModelUnit_weak p r)).at t ≫
        rowLoopMap (evaluationInverseModel (X := op A.obj.right) A.obj.hom) :=
  rowTransformationSpectrumHomotopy_postcomp_at (tensorModelUnit p r)
    (tensorModelUnit_weak p r) (evaluationInverseModel (X := op A.obj.right) A.obj.hom) t

end Quillen.PerfectComplexes.SupportedTensorEvaluation
