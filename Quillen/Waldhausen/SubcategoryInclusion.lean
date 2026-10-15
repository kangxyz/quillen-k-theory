/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Quillen.Waldhausen.ComplexSubcategory
public import Quillen.Waldhausen.PointedFunctor

/-!
# Inclusions between Waldhausen subcategories of complexes

An inclusion of replete extension-closed full subcategories containing zero
preserves the actual cofibrations and quasi-isomorphisms. The maps below are
constructed; no assertion of equivalence or of localization is made.
-/
@[expose] public section

open CategoryTheory.ExactCategory


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits

universe v u

attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.Waldhausen

variable {A : Type u} [Category.{v} A] [Abelian A]
  (P Q : ObjectProperty (CochainComplex A ℤ))
  [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure (CochainComplex A ℤ)).IsExtensionClosed P]
  [P.IsClosedUnderFiniteProducts]
  [Q.ContainsZero] [Q.IsClosedUnderIsomorphisms]
  [(abelianExactStructure (CochainComplex A ℤ)).IsExtensionClosed Q]
  [Q.IsClosedUnderFiniteProducts]
  (h : P ≤ Q)

instance subcategoryInclusion_additive : (ObjectProperty.ιOfLE h).Additive where

/-- The inclusion preserves inherited short exact sequences. -/
def subcategoryExactInclusion :
    CategoryTheory.ExactCategory.ExactFunctor
      (ExactSubcategory.exactStructure (abelianExactStructure (CochainComplex A ℤ)) P)
      (ExactSubcategory.exactStructure (abelianExactStructure (CochainComplex A ℤ)) Q) where
  toFunctor := ObjectProperty.ιOfLE h
  map_conflation _ hS := hS

/-- An inclusion of these full subcategories is Waldhausen-exact. -/
theorem subcategoryInclusion_exact :
    IsExact (complexSubcategory P).cof (complexSubcategory P).weq
      (complexSubcategory Q).cof (complexSubcategory Q).weq (ObjectProperty.ιOfLE h) where
  zero hZ := (ObjectProperty.ιOfLE h).map_isZero hZ
  cofibration f hf := (subcategoryExactInclusion P Q h).map_inflation f hf
  weak _ hf := hf
  pushout hi hs := by
    apply IsPushout.of_map_of_faithful Q.ι
    exact fullSubcategory_map_pushout (abelianExactStructure (CochainComplex A ℤ)) P hi hs

/-- The actual K-homomorphism induced by the inclusion. -/
def subcategoryKMap (n : ℕ) : (complexSubcategory P).K n →* (complexSubcategory Q).K n :=
  KMap (subcategoryInclusion_exact P Q h) n

end Quillen.Waldhausen
