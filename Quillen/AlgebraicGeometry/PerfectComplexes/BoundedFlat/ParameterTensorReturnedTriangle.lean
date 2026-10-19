/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterTensorReturnedCounit
public import Quillen.Waldhausen.SConstruction.Iterated.ExactModelEquivalenceTriangle

/-! # Returning and reevaluating retains the specified original functor isomorphism

The actual unit/counit triangle recovers the original movement, rather than
merely an isomorphic endpoint or a commuting scalar operation.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open Quillen.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u
namespace Quillen.PerfectComplexes.ParameterTensorEvaluationRow

/-- The original triangle identifies the full returned-then-evaluated movement. -/
theorem returnIso_counit
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (F : C ⥤ D) (A : D ⥤ E) (B : E ⥤ D) (G : C ⥤ E)
    (j : A ⋙ B ≅ 𝟭 D) (k : B ⋙ A ≅ 𝟭 E) (e : F ⋙ A ≅ G)
    (h : ∀ X, A.map (j.inv.app X) ≫ k.hom.app (A.obj X) = 𝟙 (A.obj X)) :
    whiskerRight (returnIso F A B G j e).hom A ≫
      (returnCounit G B A k).hom = e.hom := by
  ext X
  simp only [returnIso, returnCounit, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, whiskerRight_app, isoWhiskerLeft_hom, isoWhiskerRight_hom,
    whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.rightUnitor_hom_app, Functor.rightUnitor_inv_app, Category.id_comp,
    Functor.map_comp]
  have hk : A.map (B.map (e.hom.app X)) ≫ k.hom.app (G.obj X) =
      k.hom.app (A.obj (F.obj X)) ≫ e.hom.app X := k.hom.naturality (e.hom.app X)
  simp only [Category.assoc]
  change A.map (j.inv.app (F.obj X)) ≫
    (A.map (B.map (e.hom.app X)) ≫ (k.hom.app (G.obj X) ≫ 𝟙 (G.obj X))) = e.hom.app X
  exact (congrArg
    (fun z => A.map (j.inv.app (F.obj X)) ≫ (A.map (B.map (e.hom.app X)) ≫ z))
    (Category.comp_id (k.hom.app (G.obj X)))).trans
      ((congrArg (fun z => A.map (j.inv.app (F.obj X)) ≫ z) hk).trans
        ((Category.assoc (A.map (j.inv.app (F.obj X)))
          (k.hom.app (A.obj (F.obj X))) (e.hom.app X)).symm.trans
          ((congrArg (fun z => z ≫ e.hom.app X) (h (F.obj X))).trans
            (Category.id_comp (e.hom.app X)))))

/-- The actual zero-normalized inverse recovers any specified original comparison. -/
theorem returnIso_counit_exact
    {C : Type*} [Category* C] {V W : Model.{u}} (e : V ≌ W)
    (hF : Quillen.Waldhausen.IsExact V.waldhausen.cof V.waldhausen.weq
      W.waldhausen.cof W.waldhausen.weq e.functor)
    (hG : Quillen.Waldhausen.IsExact W.waldhausen.cof W.waldhausen.weq
      V.waldhausen.cof V.waldhausen.weq e.inverse)
    (h0 : e.functor.obj V.waldhausen.zero = W.waldhausen.zero)
    (F : C ⥤ V) (G : C ⥤ W)
    (j : F ⋙ (ExactModelEquivalence.forward e hF h0).functor ≅ G) :
    whiskerRight
        (returnIso F (ExactModelEquivalence.forward e hF h0).functor
          (ExactModelEquivalence.backward e hG).functor G
          (ExactModelEquivalence.unitIso e hF hG h0) j).hom
        (ExactModelEquivalence.forward e hF h0).functor ≫
      (returnCounit G (ExactModelEquivalence.backward e hG).functor
        (ExactModelEquivalence.forward e hF h0).functor
        (ExactModelEquivalence.counitIso e hF hG h0)).hom = j.hom :=
  returnIso_counit _ _ _ _ _ _ _
    (ExactModelEquivalence.forward_unit_counit e hF hG h0)

open GlobalSectionChangeIndex

/-- Returning and then evaluating the genuine tensor comparison recovers that exact comparison. -/
theorem returnedTensorIso_evaluation (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :
    whiskerRight (returnedTensorIso Q X).hom
        (evaluationModel (op (scheme Q (laurent.op.obj X)))).functor ≫
      (returnedTensorEvaluationIso Q X).hom = (internalTensorModelIso Q X).hom :=
  returnIso_counit_exact (evaluationModelEquivalence (op (scheme Q (laurent.op.obj X))))
    (evaluationModel (op (scheme Q (laurent.op.obj X)))).exact
    (evaluationSmallEquivalence_inverse_exact (op (scheme Q (laurent.op.obj X))))
    (evaluationModel (op (scheme Q (laurent.op.obj X)))).zero
    (globalModel.map (coefficientMap Q X).op).functor (tensorModelMap Q X).functor
    (internalTensorModelIso Q X)

end Quillen.PerfectComplexes.ParameterTensorEvaluationRow
