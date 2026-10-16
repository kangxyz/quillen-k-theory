/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Quillen.Aglib.Algebra.Homology.CochainComplex.SplitFactorization.ComplexQuotient
public import Quillen.Aglib.Algebra.Homology.CochainComplex.SplitFactorization.SubcategoryFunctor
public import Aglib.CategoryTheory.ExactCategory.Subcategory

/-!
# The actual two endpoints and their inherited inclusion

The original biproduct endpoint object and joint inclusion lift to the
cone-closed full complex subcategory with their stated closure hypotheses.
-/
@[expose] public section

open CategoryTheory.ExactCategory


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits CochainComplex
universe v u

namespace Quillen.Waldhausen.SplitFactorization

attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [Category.{v} A] [Abelian A]
  (P : ObjectProperty (CochainComplex A ℤ))
  [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure (CochainComplex A ℤ)).IsExtensionClosed P]
  [P.IsClosedUnderFiniteProducts]
  (hcone : ∀ {K L : CochainComplex A ℤ}, P K → P L →
    ∀ f : K ⟶ L, P (mappingCone f))
  (hshift : ∀ K, P K → P (K⟦(1 : ℤ)⟧))

/-- The two actual endpoints as an inherited object. -/
def subcategoryJointSource (f : Arrow P.FullSubcategory) : P.FullSubcategory :=
  ⟨f.left.obj ⊞ f.right.obj,
    (abelianExactStructure (CochainComplex A ℤ)).prop_biprod P f.left.property f.right.property⟩

/-- Both original endpoints into the original factorization object. -/
def subcategoryJointInclusion (f : Arrow P.FullSubcategory) :
    subcategoryJointSource P f ⟶ (subcategoryMiddleFunctor P hcone).obj f :=
  P.homMk (jointInclusion f.hom.hom)

end Quillen.Waldhausen.SplitFactorization
