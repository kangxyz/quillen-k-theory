/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.AlgebraicGeometry.Scheme.Coherent.PrincipalRestriction
public import Quillen.Localization.SmallModel

/-!
# Actual global coherent support in the principal-open small model

The support category used by the small-model localization theorem is
explicitly equivalent to the actual global coherent sheaves supported away
from the principal open. The resulting K-equivalence uses the same upper
universe as the public global `G` and `SupportedG` definitions.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.CoherentScheme

variable (R : CommRingCat.{u}) [IsNoetherianRing R] (r : R)

/-- Actual global coherent restriction in the upper-universe small models. -/
abbrev coherentPrincipalSmallRestriction :=
  SmallModelLocalization.functor.{u + 1} (finiteTypeSheavesRestriction (principalOpen R r))

/-- Its actual kernel property. -/
abbrev coherentPrincipalSmallSupport := (coherentPrincipalSmallRestriction R r).kernel

/-- Membership means that the represented actual sheaf vanishes on the open. -/
theorem coherentPrincipalSmallSupport_iff (M : SmallModel.{u + 1} (FiniteTypeSheaves (Spec R))) :
    coherentPrincipalSmallSupport R r M ↔
      finiteTypeSheavesSupportedAway (principalOpen R r)
        ((equivSmallModel.{u + 1} (FiniteTypeSheaves (Spec R))).inverse.obj M) := by
  have h := SmallModelLocalization.kernel_iff.{u + 1}
    (finiteTypeSheavesRestriction (principalOpen R r)) M
  rw [finiteTypeSheavesRestriction_kernel_eq_support] at h
  exact h

/-- The compatible support category is an actual small presentation of the
geometric supported coherent category. -/
def coherentPrincipalSmallSupportEquivalence :
    (coherentPrincipalSmallSupport R r).FullSubcategory ≌
      SupportedFiniteTypeSheaves (principalOpen R r) :=
  (equivSmallModel.{u + 1} (FiniteTypeSheaves (Spec R))).symm.congrFullSubcategory (by
    funext M
    apply propext
    exact (coherentPrincipalSmallSupport_iff R r M).symm)

/-- The principal support category is abelian under the actual noetherian-ring
hypothesis, using its Serre-class closure properties. -/
instance instAbelianCoherentPrincipalSmallSupport :
    Abelian (coherentPrincipalSmallSupport R r).FullSubcategory :=
  Devissage.subcategoryAbelian (coherentPrincipalSmallSupport R r)

/-- The compatible supported K-term in the upper universe. -/
abbrev CoherentPrincipalSupportedG (n : ℕ) : Type (u + 1) :=
  (abelianExactStructure (coherentPrincipalSmallSupport R r).FullSubcategory).K n

/-- The comparison between the two actual small support presentations. -/
def coherentPrincipalSupportSmallModelEquivalence :
    SmallModel.{u + 1} (SupportedFiniteTypeSheaves (principalOpen R r)) ≌
      (coherentPrincipalSmallSupport R r).FullSubcategory :=
  (equivSmallModel.{u + 1} (SupportedFiniteTypeSheaves (principalOpen R r))).symm.trans
    (coherentPrincipalSmallSupportEquivalence R r).symm

instance coherentPrincipalSupportSmallModelEquivalence_additive :
    (coherentPrincipalSupportSmallModelEquivalence R r).functor.Additive := by
  let := preservesBinaryBiproducts_of_preservesBinaryProducts
    (coherentPrincipalSupportSmallModelEquivalence R r).functor
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- The exact comparison of support presentations. -/
def coherentPrincipalSupportComparison :
    ExactFunctor (supportedCoherentExactStructure (principalOpen R r)).smallModel
      (abelianExactStructure (coherentPrincipalSmallSupport R r).FullSubcategory) where
  toFunctor := (coherentPrincipalSupportSmallModelEquivalence R r).functor
  map_conflation S h := by
    change (abelianExactStructure
      (SupportedFiniteTypeSheaves (principalOpen R r))).smallModel.conflation S at h
    rw [abelianExactStructure_smallModel] at h
    exact h.map_of_exact _

instance coherentPrincipalSupportComparison_isEquivalence :
    (coherentPrincipalSupportComparison R r).toFunctor.IsEquivalence :=
  (coherentPrincipalSupportSmallModelEquivalence R r).isEquivalence_functor

instance coherentPrincipalSupportComparison_mapQ_isEquivalence :
    (coherentPrincipalSupportComparison R r).mapQ.IsEquivalence := by
  apply CategoryTheory.ExactCategory.ExactFunctor.mapQ_isEquivalence_of_equivalence
  · intro M N f hf
    change (abelianExactStructure
      (SupportedFiniteTypeSheaves (principalOpen R r))).smallModel.inflation f
    rw [abelianExactStructure_smallModel, abelianExactStructure_inflation_iff]
    exact (coherentPrincipalSupportComparison R r).toFunctor.mono_of_mono_map
      ((abelianExactStructure_inflation_iff _ _).mp hf)
  · intro M N f hf
    change (abelianExactStructure
      (SupportedFiniteTypeSheaves (principalOpen R r))).smallModel.deflation f
    rw [abelianExactStructure_smallModel, abelianExactStructure_deflation_iff]
    exact (coherentPrincipalSupportComparison R r).toFunctor.epi_of_epi_map
      ((abelianExactStructure_deflation_iff _ _).mp hf)

/-- The public actual supported G-group agrees with the compatible support
term of the localization theorem, in the same universe. -/
def coherentPrincipalSupportedGEquiv (n : ℕ) :
    SupportedG (principalOpen R r) n ≃* CoherentPrincipalSupportedG R r n :=
  (coherentPrincipalSupportComparison R r).KEquivOfMapQIsEquivalence n

end Quillen.CoherentScheme
