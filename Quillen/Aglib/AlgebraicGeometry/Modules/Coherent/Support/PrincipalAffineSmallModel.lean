/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.Coherent.Affine.RestrictionExact
public import Aglib.AlgebraicGeometry.Modules.Coherent.Affine.Support
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FiniteTypeCategory
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FiniteTypeRestriction
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FiniteTypeSupport
public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Aglib.CategoryTheory.ExactCategory.Functor
public import Aglib.CategoryTheory.SmallModel.Abelian
public import Aglib.AlgebraicGeometry.Modules.Coherent.Localization.Principal
public import Aglib.CategoryTheory.SmallModel.Functor

/-!
# The principal affine supported small model

On a noetherian spectrum, the kernel of small-model principal-open restriction is an exact categorical presentation of the actual coherent sheaves supported on the complement.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Coherent
open CategoryTheory.ExactCategory

open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules.Coherent

variable (R : CommRingCat.{u}) [IsNoetherianRing R] (r : R)

/-- The actual principal-open restriction in the chosen small coherent models. -/

abbrev principalSmallRestriction :=
  CategoryTheory.SmallModel.functor.{u} (affinePrincipalRestriction R r)

/-- The support property on that small model. -/

abbrev principalSmallSupport := (principalSmallRestriction R r).kernel

/-- Membership still means ordinary stalk support in the actual closed
complement for the represented coherent sheaf. -/

theorem principalSmallSupport_iff (M : SmallModel.{u} (AffineFiniteType R)) :
    principalSmallSupport R r M ↔
      affineSupportedAway R (principalOpen R r)
        ((equivSmallModel (AffineFiniteType R)).inverse.obj M) := by
  have h := CategoryTheory.SmallModel.kernel_iff.{u} (affinePrincipalRestriction R r) M
  rw [principalRestriction_kernel_eq_support] at h
  exact h

/-- The small support category is genuinely a presentation of the actual
supported coherent sheaf category. -/

def principalSmallSupportEquivalence :
    (principalSmallSupport R r).FullSubcategory ≌
      SupportedAffineFiniteType R (principalOpen R r) :=
  (equivSmallModel.{u} (AffineFiniteType R)).symm.congrFullSubcategory (by
    funext M
    apply propext
    exact (principalSmallSupport_iff R r M).symm)

/-- Its forward functor commutes with actual supported-sheaf inclusion.
The underlying functors are equal by definition. -/

theorem principalSmallSupportEquivalence_comp_inclusion :
    (principalSmallSupportEquivalence R r).functor ⋙
        (affineSupportedAway R (principalOpen R r)).ι =
      (principalSmallSupport R r).ι ⋙ (equivSmallModel (AffineFiniteType R)).inverse := rfl

/-- This is a genuine small presentation comparison with the previously
chosen small model of actual supported coherent sheaves. -/

def principalSupportSmallModelEquivalence :
    SmallModel.{u} (SupportedAffineFiniteType R (principalOpen R r)) ≌
      (principalSmallSupport R r).FullSubcategory :=
  (equivSmallModel (SupportedAffineFiniteType R (principalOpen R r))).symm.trans
    (principalSmallSupportEquivalence R r).symm

instance principalSupportSmallModelEquivalence_additive :
    (principalSupportSmallModelEquivalence R r).functor.Additive := by
  let := preservesBinaryBiproducts_of_preservesBinaryProducts
    (principalSupportSmallModelEquivalence R r).functor
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- The actual exact comparison of the two small supported presentations. -/

def principalSupportComparison :
    ExactFunctor (supportedAffineCoherentExactStructure R (principalOpen R r)).smallModel
      (abelianExactStructure (principalSmallSupport R r).FullSubcategory) where
  toFunctor := (principalSupportSmallModelEquivalence R r).functor
  map_conflation S h := by
    change (abelianExactStructure (SupportedAffineFiniteType R (principalOpen R
      r))).smallModel.conflation S at h
    rw [abelianExactStructure_smallModel] at h
    exact h.map_of_exact _

instance principalSupportComparison_isEquivalence :
    (principalSupportComparison R r).toFunctor.IsEquivalence :=
  (principalSupportSmallModelEquivalence R r).isEquivalence_functor

end AlgebraicGeometry.Scheme.Modules.Coherent
