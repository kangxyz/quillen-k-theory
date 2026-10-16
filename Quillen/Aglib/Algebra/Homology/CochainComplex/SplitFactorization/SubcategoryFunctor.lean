/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Quillen.Aglib.Algebra.Homology.CochainComplex.SplitFactorization.Subcategory
public import Quillen.Aglib.Algebra.Homology.CochainComplex.SplitFactorization.FactorizationFunctor

/-!
# The actual middle-object functor in a cone-closed full subcategory

The original arrow-category middle functor lifts to the stated exact full
subcategory without changing its objects or chain maps.
-/
@[expose] public section

open CategoryTheory.ExactCategory



noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits CochainComplex

universe v u

namespace Quillen.Waldhausen

variable {A : Type u} [Category.{v} A] [Abelian A]

attribute [local instance] Abelian.hasFiniteBiproducts

variable (P : ObjectProperty (CochainComplex A ℤ))
  [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure (CochainComplex A ℤ)).IsExtensionClosed P]
  [P.IsClosedUnderFiniteProducts]
  (hcone : ∀ {K L : CochainComplex A ℤ}, P K → P L →
    ∀ f : K ⟶ L, P (mappingCone f))

/-- The explicit middle-object functor, restricted to the actual full subcategory. -/
def subcategoryMiddleFunctor : Arrow P.FullSubcategory ⥤ P.FullSubcategory :=
  P.lift (P.ι.mapArrow ⋙ SplitFactorization.middleFunctor)
    (fun f ↦ SplitFactorization.middle_property P hcone f.left.property f.right.property f.hom.hom)

end Quillen.Waldhausen

end
