/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorLaurentUnit
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalSupportedPairReindex

/-!
# Genuine tensor-unit transport through global evaluation

The original tensor unitor and section evaluation transition give the actual comparison.
Its automorphism square keeps the same scalar and the original section unit.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.GlobalSectionChangeIndex

attribute [local irreducible] globalEvaluation boundedFlatPerfectGlobalUnitIso

/-- Tensor pullback followed by its actual unitor and original evaluation transition. -/
def tensorEvaluationIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    globalEvaluation (Opposite.op Y) ⋙ boundedFlatPerfectTensorUnitPullback f ≅
      (globalModel.map f.op).functor ⋙ globalEvaluation (Opposite.op X) :=
  Functor.isoWhiskerLeft _ (boundedFlatPerfectTensorUnitPullbackIso f) ≪≫
    evaluationPullbackIso f

/-- The genuine tensor automorphism transports to the original evaluated global unit. -/
theorem tensorEvaluation_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (r : (Γ(X, ⊤))ˣ) :
    Functor.whiskerLeft (globalEvaluation (Opposite.op Y))
        (boundedFlatPerfectTensorUnitPullbackAutomorphism f r).hom ≫
      (tensorEvaluationIso f).hom =
    (tensorEvaluationIso f).hom ≫
      Functor.whiskerRight
        (Functor.whiskerLeft (globalModel.map f.op).functor
          (globalUnit (Opposite.op X) r).hom) (globalEvaluation (Opposite.op X)) := by
  apply NatTrans.ext
  funext S
  change (boundedFlatPerfectTensorUnitPullbackAutomorphism f r).hom.app _ ≫
      ((boundedFlatPerfectTensorUnitPullbackIso f).hom.app _ ≫
        (evaluationPullbackIso f).hom.app S) =
    ((boundedFlatPerfectTensorUnitPullbackIso f).hom.app _ ≫
        (evaluationPullbackIso f).hom.app S) ≫ _
  have hu := NatTrans.congr_app
    (boundedFlatPerfectTensorUnitPullbackAutomorphism_unitor f r)
    ((globalEvaluation (Opposite.op Y)).obj S)
  simp only [NatTrans.comp_app] at hu
  rw [← Category.assoc, hu]
  simp only [Category.assoc, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  have he := globalUnit_evaluation (Opposite.op X) r
    ((globalModel.map f.op).functor.obj S)
  rw [he]
  congr 1
  simpa only [boundedFlatPerfectPullbackUnitIso, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.id_map, Functor.id_obj, Functor.comp_obj, Iso.trans_hom,
    Iso.symm_hom, NatTrans.comp_app, Functor.rightUnitor_inv_app,
    Functor.rightUnitor_hom_app, Category.id_comp, Category.comp_id] using
    ((boundedFlatPerfectGlobalUnitIso X r).hom.naturality
      ((evaluationPullbackIso f).hom.app S)).symm

end Quillen.PerfectComplexes.GlobalSectionChangeIndex
