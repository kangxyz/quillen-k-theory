/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.SplitComplexes.FactorizationCofiber
public import Quillen.Waldhausen.GrothendieckComparison.LargeCofiberRelations

/-!
# The original signed mapping-cone class

For an arbitrary arrow in a cone-closed full complex subcategory, the actual
split factorization gives a cofibration with the original signed cone as its
quotient. Its actual projection is a weak equivalence to the original target.
The resulting K-zero relation uses unchanged original object classes and
requires no cofibration hypothesis on the given arrow.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits CochainComplex
universe u v
namespace Quillen.Waldhausen.SplitFactorization
variable {A : Type u} [Category.{v} A] [Abelian A]
attribute [local instance] Abelian.hasFiniteBiproducts
variable (P : ObjectProperty (CochainComplex A ℤ))
  [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(_root_.CategoryTheory.ExactCategory.abelianExactStructure
    (CochainComplex A ℤ)).IsExtensionClosed P]
  [P.IsClosedUnderFiniteProducts]
  (hcone : ∀ {K L : CochainComplex A ℤ}, P K → P L → ∀ f : K ⟶ L, P (mappingCone f))
  {K L : P.FullSubcategory} (f : K ⟶ L)

/-- The actual weak projection identifies the factorization middle with its original target. -/
theorem subcategoryMiddle_kZeroObjectClass :
    (complexSubcategory P).kZeroObjectClass
        ((ExtensionCategory.middle (complexSubcategory P)).obj
          (subcategoryExtension P hcone f)) =
      (complexSubcategory P).kZeroObjectClass L := by
  exact (complexSubcategory P).kZeroObjectClass_weak
    ((splitSubcategoryFunctorialFactorization P hcone).projection.app (Arrow.mk f))
    ((splitSubcategoryFunctorialFactorization P hcone).weak (Arrow.mk f))

/-- The original signed cone has target class times inverse source class, for any arrow. -/
theorem subcategoryCone_kZeroObjectClass :
    (complexSubcategory P).kZeroObjectClass (subcategoryConeObject P hcone f) =
      (complexSubcategory P).kZeroObjectClass L *
        ((complexSubcategory P).kZeroObjectClass K)⁻¹ := by
  let : CommGroup ((complexSubcategory P).K 0) := Additivity.KCommGroup (complexSubcategory P) 0
  have hc := (complexSubcategory P).kZeroObjectClass_cofiber_of_large
    (((splitSubcategoryFunctorialFactorization P hcone).cofibration (Arrow.mk f)).1)
    (subcategoryCone_isPushout P hcone f)
  have ht : (complexSubcategory P).kZeroObjectClass L =
      (complexSubcategory P).kZeroObjectClass K *
        (complexSubcategory P).kZeroObjectClass (subcategoryConeObject P hcone f) :=
    (subcategoryMiddle_kZeroObjectClass P hcone f).symm.trans hc
  rw [ht]
  simp [mul_comm, mul_left_comm]

end Quillen.Waldhausen.SplitFactorization
