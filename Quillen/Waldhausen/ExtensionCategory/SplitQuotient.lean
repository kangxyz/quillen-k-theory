/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Waldhausen.ExtensionCategory.Split

/-! # The exact source/cofiber composite on split extensions -/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Quillen.Waldhausen.ExtensionCategory
variable {C : Type u} [Category.{v} C] (W : Structure C) [HasBinaryCoproducts C]

/-- The literal projection from `C ⨿ A` onto `C`, through zero on `A`. -/
def splitProjection : split W ⋙ middle W ⟶ CategoryTheory.Prod.snd C C :=
  Additivity.sumProjection W (CategoryTheory.Prod.snd C C) (CategoryTheory.Prod.fst C C)

/-- The actual cofiber of the split extension is its displayed quotient summand. -/
def splitCofiberIso (X : C × C) : (cofiber W).obj ((split W).obj X) ≅ X.2 :=
  (cofiber_isPushout W ((split W).obj X)).isoIsPushout _ _
    (Additivity.coprod_inr_cofiber W X.2 X.1)

@[reassoc (attr := simp)] theorem quotient_splitCofiberIso (X : C × C) :
    (quotient W).app ((split W).obj X) ≫ (splitCofiberIso W X).hom = (splitProjection W).app X :=
  (cofiber_isPushout W ((split W).obj X)).inl_isoIsPushout_hom _ _
    (Additivity.coprod_inr_cofiber W X.2 X.1)

/-- The actual split cofiber identification is natural in both original summands. -/
def splitCofiberNatIso : split W ⋙ cofiber W ≅ CategoryTheory.Prod.snd C C :=
  NatIso.ofComponents (splitCofiberIso W) (by
    intro X Y f
    apply (cofiber_isPushout W ((split W).obj X)).hom_ext
    · change (quotient W).app ((split W).obj X) ≫
        (cofiber W).map ((split W).map f) ≫ (splitCofiberIso W Y).hom =
          (quotient W).app ((split W).obj X) ≫ (splitCofiberIso W X).hom ≫ f.2
      rw [← Category.assoc, ← (quotient W).naturality ((split W).map f), Category.assoc,
        quotient_splitCofiberIso, ← Category.assoc, quotient_splitCofiberIso]
      exact (splitProjection W).naturality f
    · exact W.isZero.eq_of_src _ _)

/-- Splitting followed by source/cofiber is naturally the identity on the
actual product category. No realization/product identification occurs here. -/
def splitSourceCofiberIso : split W ⋙ sourceCofiber W ≅ 𝟭 (C × C) :=
  NatIso.ofComponents (fun X ↦
    (Iso.prod (Iso.refl X.1) (splitCofiberIso W X)) ≪≫ CategoryTheory.prod.etaIso X) (by
      intro X Y f
      apply _root_.Prod.ext
      · simp [sourceCofiber, source, forget, split, CategoryTheory.prod.etaIso]
      · simpa using! (splitCofiberNatIso W).hom.naturality f)

end Quillen.Waldhausen.ExtensionCategory
