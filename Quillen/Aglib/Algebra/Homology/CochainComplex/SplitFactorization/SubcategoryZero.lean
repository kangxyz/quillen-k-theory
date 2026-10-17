/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Quillen.Waldhausen.ArrowCategory.Structure
public import Quillen.Waldhausen.ComplexSubcategory
public import Quillen.Aglib.Algebra.Homology.CochainComplex.SplitFactorization.JointSubcategory
public import Quillen.Aglib.Algebra.Homology.CochainComplex.SplitFactorization.ZeroEndpoint
public import Quillen.Aglib.Algebra.Homology.CochainComplex.SplitFactorization.Pushout

/-!
# Zero preservation of the restricted middle-object functor

The original identity-cone middle functor preserves actual zero endpoints and
zero arrows in the stated cone-closed full complex subcategory.
-/
@[expose] public section

open CategoryTheory.ExactCategory



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits CochainComplex
universe u v

namespace Quillen.Waldhausen.SplitFactorization
attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [Category.{v} A] [Abelian A]
  (P : ObjectProperty (CochainComplex A ℤ))
  [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure (CochainComplex A ℤ)).IsExtensionClosed P]
  [P.IsClosedUnderFiniteProducts]
  (hcone : ∀ {K L : CochainComplex A ℤ}, P K → P L →
    ∀ f : K ⟶ L, P (mappingCone f))

omit [P.ContainsZero] [P.IsClosedUnderIsomorphisms] [P.IsClosedUnderFiniteProducts] in
/-- A cylinder with two genuinely zero endpoints is genuinely zero. -/
theorem subcategoryMiddleFunctor_obj_isZero {f : Arrow P.FullSubcategory}
    (hl : IsZero f.left) (hr : IsZero f.right) :
    IsZero ((subcategoryMiddleFunctor P hcone).obj f) := by
  have hm : IsZero ((subcategoryMiddleFunctor P hcone).obj f).obj :=
    (P.ι.map_isZero hr).of_iso
      (projectionIsoOfIsZeroSource f.hom.hom (P.ι.map_isZero hl))
  rw [IsZero.iff_id_eq_zero]
  apply ObjectProperty.hom_ext
  exact hm.eq_of_src _ _

/-- Every genuine zero object of the entire arrow category is preserved. -/
theorem subcategoryMiddleFunctor_zero {f : Arrow P.FullSubcategory} (hf : IsZero f) :
    IsZero ((subcategoryMiddleFunctor P hcone).obj f) :=
  subcategoryMiddleFunctor_obj_isZero P hcone
    ((ArrowCategory.source_exact (complexSubcategory P)).zero hf)
    ((ArrowCategory.target_exact (complexSubcategory P)).zero hf)

end Quillen.Waldhausen.SplitFactorization
