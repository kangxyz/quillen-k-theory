/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedPullbackForgetComparison

/-! # Whole geometric isomorphisms under the original support inclusion

The original geometric composition and equality-transport isomorphisms retain their actual
ambient isomorphisms after forgetting support. These whole-isomorphism formulas avoid
expanding the concrete geometric components of longer input routes.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes

/-- The entire original composition comparison is preserved by support-forgetting. -/
theorem boundedFlatPerfectSupportedPullbackCompIso_forget
    {A B C : Scheme.OpenPairs.{u}} (f : A ⟶ B) (g : B ⟶ C) :
    isoWhiskerRight (boundedFlatPerfectSupportedPullbackCompIso f g)
        (tensorCoefficientSupportedForget A.obj.hom) =
      isoWhiskerLeft (tensorCoefficientSupportedForget C.obj.hom)
        (boundedFlatPerfectPullbackCompIso f.hom.right g.hom.right) := by
  apply Iso.ext
  apply NatTrans.ext
  funext K
  exact boundedFlatPerfectSupportedPullbackCompIso_forget_hom_app f g K

namespace GlobalSectionChangeIndex

/-- The entire original equality transport is preserved by the genuine support inclusion. -/
theorem supportedPullbackEquality_forget_iso {A B : Scheme.OpenPairs.{u}}
    {f g : A ⟶ B} (h : f = g) :
    isoWhiskerRight (eqToIso (congrArg boundedFlatPerfectSupportedPullback h))
        (tensorCoefficientSupportedForget A.obj.hom) =
      isoWhiskerLeft (tensorCoefficientSupportedForget B.obj.hom)
        (eqToIso (congrArg (fun k : A ⟶ B => boundedFlatPerfectPullback k.hom.right) h)) := by
  subst g
  simp only [eqToIso_refl, isoWhiskerRight_refl, isoWhiskerLeft_refl]
  rfl

end GlobalSectionChangeIndex
end Quillen.PerfectComplexes
