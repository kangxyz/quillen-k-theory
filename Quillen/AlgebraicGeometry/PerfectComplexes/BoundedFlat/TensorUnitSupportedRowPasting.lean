/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitSupportedModelUnit
public import Quillen.Waldhausen.SConstruction.Iterated.RowTransformationPasting

/-! # The actual supported tensor/evaluation endpoint-relative first-row prism -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS Quillen.FunctorIdentityAutomorphism
universe u
namespace Quillen.PerfectComplexes.SupportedTensorEvaluation
open GlobalSectionChangeIndex
variable {A B : Scheme.OpenPairs.{u}} (p : A ⟶ B) (r : (Γ(A.obj.right, ⊤))ˣ)

/-- The original internal supported scalar after actual target evaluation. -/
def internalModelUnit : (internalModelMap p).functor ⟶ (internalModelMap p).functor :=
  whiskerRight
    (onFunctor (supportedPairModelMap p).functor
      (unit (X := op A.obj.right) A.obj.hom r)).hom
    (evaluationModel (X := op A.obj.right) A.obj.hom).functor

/-- The genuine supported tensor crossing after original source evaluation. -/
def tensorModelUnit : (tensorModelMap p).functor ⟶ (tensorModelMap p).functor :=
  whiskerLeft (evaluationModel (X := op B.obj.right) B.obj.hom).functor
    (tensorSupportedPairModelTransformation p r)

/-- Exact supported evaluation retains the internal unit's original weak equivalence. -/
theorem internalModelUnit_weak
    (K : supportedModel (X := op B.obj.right) B.obj.hom) :
    (modelOf (boundedFlatPerfectSupportedWaldhausen A.obj.hom)).waldhausen.weq
      ((internalModelUnit p r).app K) :=
  (evaluationModel (X := op A.obj.right) A.obj.hom).exact.weak _
    ((supportedModel (X := op A.obj.right) A.obj.hom).waldhausen.weq_iso _ inferInstance)

/-- Actual supported source evaluation retains the genuine tensor weak crossing. -/
theorem tensorModelUnit_weak
    (K : supportedModel (X := op B.obj.right) B.obj.hom) :
    (modelOf (boundedFlatPerfectSupportedWaldhausen A.obj.hom)).waldhausen.weq
      ((tensorModelUnit p r).app K) :=
  tensorSupportedPairModelTransformation_weak p r
    ((evaluationModel (X := op B.obj.right) B.obj.hom).functor.obj K)

/-- The complete supported first-row prism retains its real endpoint comparison paths. -/
def tensorRowPasting :=
  rowTransformationPasting
    (F := internalModelMap p) (G := internalModelMap p)
    (G' := tensorModelMap p) (H := tensorModelMap p)
    (internalModelUnit p r) (internalTensorModelIso p).hom
    (internalTensorModelIso p).hom (tensorModelUnit p r)
    (internalModelUnit_weak p r)
    (fun _ => (modelOf (boundedFlatPerfectSupportedWaldhausen A.obj.hom)).waldhausen.weq_iso
      _ inferInstance)
    (fun _ => (modelOf (boundedFlatPerfectSupportedWaldhausen A.obj.hom)).waldhausen.weq_iso
      _ inferInstance)
    (tensorModelUnit_weak p r) (internalTensorModelIso_unit p r)

end Quillen.PerfectComplexes.SupportedTensorEvaluation
