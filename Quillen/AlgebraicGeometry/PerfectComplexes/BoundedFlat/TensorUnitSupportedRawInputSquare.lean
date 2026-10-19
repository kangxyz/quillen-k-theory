/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitSupportedModelUnit
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedGlobalUnitIdentityOperation

/-! # The genuine supported tensor-unit square on an original pair square

The original supported tensor unitors and geometric pullback composition isomorphisms form
this comparison inside the unchanged supported full subcategories. Its whole multiplication
square uses the actual pulled-back scalar, independently of any evaluation inverse.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes
variable {A B C D : Scheme.OpenPairs.{u}}
  (p : A ⟶ B) (q : C ⟶ D) (a : C ⟶ A) (b : D ⟶ B) (h : a ≫ p = q ≫ b)

/-- The raw supported comparison retains the original pair pullback and both tensor unitors. -/
def tensorSupportedRawInputIso :
    tensorSupportedPairFunctor p ⋙ boundedFlatPerfectSupportedPullback a ≅
      boundedFlatPerfectSupportedPullback b ⋙ tensorSupportedPairFunctor q :=
  isoWhiskerRight (SupportedTensorEvaluation.tensorPairUnitor p)
      (boundedFlatPerfectSupportedPullback a) ≪≫
    (boundedFlatPerfectSupportedPullbackCompIso a p).symm ≪≫
    eqToIso (congrArg boundedFlatPerfectSupportedPullback h) ≪≫
    boundedFlatPerfectSupportedPullbackCompIso q b ≪≫
    isoWhiskerLeft (boundedFlatPerfectSupportedPullback b)
      (SupportedTensorEvaluation.tensorPairUnitor q).symm

/-- Genuine tensor multiplication respects the complete original supported input square. -/
theorem tensorSupportedRawInputIso_unit (r : (Γ(A.obj.right, ⊤))ˣ) :
    whiskerRight (tensorSupportedPairAutomorphism p r).hom
        (boundedFlatPerfectSupportedPullback a) ≫ (tensorSupportedRawInputIso p q a b h).hom =
      (tensorSupportedRawInputIso p q a b h).hom ≫
        whiskerLeft (boundedFlatPerfectSupportedPullback b)
          (tensorSupportedPairAutomorphism q
            (Units.map a.hom.right.appTop.hom.toMonoidHom r)).hom := by
  apply NatTrans.ext
  funext K
  simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app]
  rw [SupportedTensorEvaluation.tensorAutomorphism_scalar,
    SupportedTensorEvaluation.tensorAutomorphism_scalar,
    SupportedGlobalUnitIdentityOperation.pullback_preserves a r]
  simpa only [Functor.id_map, Functor.id_obj, Functor.comp_obj] using
    ((boundedFlatPerfectSupportedGlobalUnitIso C.obj.hom
      (Units.map a.hom.right.appTop.hom.toMonoidHom r)).hom.naturality
        ((tensorSupportedRawInputIso p q a b h).hom.app K)).symm

end Quillen.PerfectComplexes
