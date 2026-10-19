/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitSupportedUnitorForget

/-! # Whole tensor unitor comparisons through genuine support inclusion

The original tensor unitor and its two geometric whiskerings keep their whole ambient
isomorphisms under the support inclusion. The proofs use the existing bounded component
comparisons without expanding any composite input square.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes.SupportedTensorEvaluation

/-- The original tensor unitor is retained as a whole isomorphism by support-forgetting. -/
theorem tensorPairUnitor_forget {A B : Scheme.OpenPairs.{u}} (p : A ⟶ B) :
    isoWhiskerRight (tensorPairUnitor p) (tensorCoefficientSupportedForget A.obj.hom) =
      isoWhiskerLeft (tensorCoefficientSupportedForget B.obj.hom)
        (boundedFlatPerfectTensorUnitPullbackIso p.hom.right) := by
  apply Iso.ext
  apply NatTrans.ext
  funext K
  exact tensorPairUnitor_forget_hom_app p K

/-- Pulling back the original tensor unitor retains its whole ambient image. -/
theorem tensorPairUnitor_whiskerRight_forget {A B C : Scheme.OpenPairs.{u}}
    (p : A ⟶ B) (a : C ⟶ A) :
    isoWhiskerRight
        (isoWhiskerRight (tensorPairUnitor p) (boundedFlatPerfectSupportedPullback a))
        (tensorCoefficientSupportedForget C.obj.hom) =
      isoWhiskerLeft (tensorCoefficientSupportedForget B.obj.hom)
        (isoWhiskerRight (boundedFlatPerfectTensorUnitPullbackIso p.hom.right)
          (boundedFlatPerfectPullback a.hom.right)) := by
  apply Iso.ext
  apply NatTrans.ext
  funext K
  exact (boundedFlatPerfectSupportedPullback_forget_map a _).trans
    (congrArg (boundedFlatPerfectPullback a.hom.right).map
      (tensorPairUnitor_forget_hom_app p K))

/-- The inverse tensor unitor on a pulled-back object retains its whole ambient image. -/
theorem tensorPairUnitor_whiskerLeft_symm_forget {B C D : Scheme.OpenPairs.{u}}
    (q : C ⟶ D) (b : D ⟶ B) :
    isoWhiskerRight
        (isoWhiskerLeft (boundedFlatPerfectSupportedPullback b) (tensorPairUnitor q).symm)
        (tensorCoefficientSupportedForget C.obj.hom) =
      isoWhiskerLeft (tensorCoefficientSupportedForget B.obj.hom)
        (isoWhiskerLeft (boundedFlatPerfectPullback b.hom.right)
          (boundedFlatPerfectTensorUnitPullbackIso q.hom.right).symm) := by
  apply Iso.ext
  apply NatTrans.ext
  funext K
  exact tensorPairUnitor_forget_inv_app q ((boundedFlatPerfectSupportedPullback b).obj K)

end Quillen.PerfectComplexes.SupportedTensorEvaluation
