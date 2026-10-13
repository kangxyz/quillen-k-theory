/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.SplitComplexes.FactorizationSign
public import Quillen.Waldhausen.SplitComplexes.FunctorialFactorization
public import Quillen.Waldhausen.ExtensionCategory.Cofiber
public import Quillen.CategoryTheory.Limits.CokernelPushout

/-!
# The original scalar-factorization cofiber as its literal mapping cone

The existing split factorization supplies an actual object of the original extension category.
Its categorical cofiber is identified with Cone(f) by the original quotient followed by the
explicit sign isomorphism from Cone(−f).
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
  [(abelianExactStructure (CochainComplex A ℤ)).IsExtensionClosed P]
  [P.IsClosedUnderFiniteProducts]
  (hcone : ∀ {K L : CochainComplex A ℤ}, P K → P L → ∀ f : K ⟶ L, P (mappingCone f))
  {K L : P.FullSubcategory} (f : K ⟶ L)

/-- The literal first factor is an original ordinary-cofibration extension object. -/
def subcategoryExtension : ExtensionCategory.Obj (complexSubcategory P) :=
  ⟨Arrow.mk ((splitSubcategoryFunctorialFactorization P hcone).inclusion.app (Arrow.mk f)),
    ((splitSubcategoryFunctorialFactorization P hcone).cofibration (Arrow.mk f)).1⟩

/-- The original cone as an object of the same full complex subcategory. -/
def subcategoryConeObject : P.FullSubcategory :=
  ⟨mappingCone f.hom, hcone K.property L.property f.hom⟩

/-- The original quotient with its explicit cone sign transport, in the original category. -/
def subcategoryConeProjection :
    (ExtensionCategory.middle (complexSubcategory P)).obj (subcategoryExtension P hcone f) ⟶
      subcategoryConeObject P hcone f :=
  P.homMk (quotientToCone f.hom)

/-- The actual signed short exact sequence gives the original categorical cofiber square. -/
theorem subcategoryCone_isPushout :
    IsPushout
      ((ExtensionCategory.inclusion (complexSubcategory P)).app (subcategoryExtension P hcone f))
      ((complexSubcategory P).isZero.from_ K)
      (subcategoryConeProjection P hcone f)
      ((complexSubcategory P).isZero.to_ (subcategoryConeObject P hcone f)) := by
  apply IsPushout.of_map_of_faithful P.ι
  let hZ := P.ι.map_isZero (complexSubcategory P).isZero
  have h := CategoryTheory.Limits.isPushout_of_isColimitCokernelCofork
    (inclusion_quotientToCone f.hom) (quotientToConeSequence_shortExact f.hom).gIsCokernel hZ
  convert h using 1 <;> first | rfl | exact hZ.eq_of_tgt _ _ | exact hZ.eq_of_src _ _

/-- The universal extension-category cofiber is the original mapping cone via its actual quotient.
-/
def subcategoryCofiberConeIso :
    (ExtensionCategory.cofiber (complexSubcategory P)).obj (subcategoryExtension P hcone f) ≅
      subcategoryConeObject P hcone f :=
  (ExtensionCategory.cofiber_isPushout (complexSubcategory P)
    (subcategoryExtension P hcone f)).isoIsPushout _ _ (subcategoryCone_isPushout P hcone f)

/-- The isomorphism intertwines the original cofiber quotient with the sign-adjusted chain map. -/
theorem subcategoryCofiberConeIso_quotient :
    (ExtensionCategory.quotient (complexSubcategory P)).app (subcategoryExtension P hcone f) ≫
        (subcategoryCofiberConeIso P hcone f).hom = subcategoryConeProjection P hcone f :=
  (ExtensionCategory.cofiber_isPushout (complexSubcategory P)
    (subcategoryExtension P hcone f)).inl_isoIsPushout_hom _ _ (subcategoryCone_isPushout P hcone f)

/-- The original target summand still maps by the literal mapping-cone inclusion. -/
theorem subcategoryConeProjection_target :
    P.homMk (biprod.inr : L.obj ⟶ middle f.hom) ≫ subcategoryConeProjection P hcone f =
      P.homMk (mappingCone.inr f.hom) := by
  apply P.ι.map_injective
  change (biprod.inr : L.obj ⟶ middle f.hom) ≫ quotientToCone f.hom = mappingCone.inr f.hom
  rw [quotientToCone, ← Category.assoc]
  simp only [quotientMap, biprod.inr_desc]
  exact Quillen.CochainComplex.mappingConeNegIso_inr f.hom

end Quillen.Waldhausen.SplitFactorization
