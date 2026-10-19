/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitSupportedReturnedInputRectangle

/-! # Arbitrary supported coefficient input and the specified return movement -/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open Quillen.PerfectComplexes Quillen.PerfectComplexes.SupportedTensorEvaluation
open Quillen.PerfectComplexes.GlobalSectionChangeIndex
universe u
namespace QuillenTest.TensorUnitSupportedReturnedInput

/-- Every original supported section retains the complete returned and raw coefficient routes. -/
theorem original_section_routes {A B C D : Scheme.OpenPairs.{u}}
    (p : A ⟶ B) (q : C ⟶ D) (a : C ⟶ A) (b : D ⟶ B) (h : a ≫ p = q ≫ b)
    (K : (supported (X := op B.obj.right) B.obj.hom).FullSubcategory) :
    (rawEvaluatedInputIso p q a b h).hom.app K ≫
        (returnedEvaluationInputRight q b).hom.app K =
      (returnedEvaluationInputLeft p a).hom.app K ≫
        (isoWhiskerRight (returnedInputIso p q a b h)
          (evaluationModel (X := op C.obj.right) C.obj.hom).functor).hom.app K :=
  NatTrans.congr_app (congrArg Iso.hom (returnedInputIso_evaluation_rectangle p q a b h)) K

end QuillenTest.TensorUnitSupportedReturnedInput
