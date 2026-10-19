/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitSupportedUnitorForget
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalTensorUnitEvaluation

/-! # Original supported tensor evaluation through the actual support inclusion

Every component of the original supported tensor evaluation comparison retains both actual
ambient factors. This identity precedes zero normalization and common-universe transport.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes
variable {A B : Scheme.OpenPairs.{u}}

namespace GlobalSectionChangeIndex
attribute [local irreducible] globalModel globalEvaluation

/-- The actual supported evaluation retains the same underlying bounded-flat object. -/
theorem supportedEvaluation_forget_obj {X : Scheme.{u}ᵒᵖ} {U : Scheme.{u}}
    (j : U ⟶ X.unop) [IsOpenImmersion j] (K : (supported j).FullSubcategory) :
    (tensorCoefficientSupportedForget j).obj ((supportedEvaluation j).obj K) =
      (globalEvaluation X).obj K.obj :=
  congrArg (fun F => F.obj K) (supportedEvaluation_forget j)

/-- The supported tensor evaluation comparison retains both original ambient factors. -/
theorem tensorEvaluationIso_forget_hom_app (p : A ⟶ B)
    (K : (supported (X := Opposite.op B.obj.right) B.obj.hom).FullSubcategory) :
    (tensorCoefficientSupportedForget A.obj.hom).map
        ((SupportedTensorEvaluation.tensorEvaluationIso p).hom.app K) =
      (tensorEvaluationIso p.hom.right).hom.app K.obj := by
  simp only [SupportedTensorEvaluation.tensorEvaluationIso, tensorEvaluationIso,
    Iso.trans_hom, NatTrans.comp_app, Functor.map_comp, isoWhiskerLeft_hom,
    whiskerLeft_app, SupportedTensorEvaluation.tensorPairUnitor_forget_hom_app,
    supportedPairReindexEvaluationIso_forget_hom_app]
  rfl

end GlobalSectionChangeIndex

end Quillen.PerfectComplexes
