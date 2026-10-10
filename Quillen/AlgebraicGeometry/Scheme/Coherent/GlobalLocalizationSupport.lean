/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.AlgebraicGeometry.Scheme.Coherent.Restriction
public import Quillen.Localization.SmallModel
public import Quillen.Devissage.Setup

/-!
# Actual global coherent support in the open-restriction small model

The support category used by the small-model localization theorem is
explicitly equivalent to the actual global coherent sheaves supported away
from the selected open. The resulting K-equivalence uses the same upper
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

variable {U X : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian U]
  (j : U ⟶ X) [IsOpenImmersion j]

/-- Actual global coherent restriction in the upper-universe small models. -/
abbrev coherentGlobalSmallRestriction :=
  SmallModelLocalization.functor.{u + 1} (finiteTypeSheavesRestriction j)

/-- Its actual kernel property. -/
abbrev coherentGlobalSmallSupport := (coherentGlobalSmallRestriction j).kernel

omit [IsLocallyNoetherian X] in
/-- Membership means that the represented actual sheaf vanishes on the open. -/
theorem coherentGlobalSmallSupport_iff (M : SmallModel.{u + 1} (FiniteTypeSheaves X)) :
    coherentGlobalSmallSupport j M ↔
      finiteTypeSheavesSupportedAway j
        ((equivSmallModel.{u + 1} (FiniteTypeSheaves X)).inverse.obj M) := by
  have h := SmallModelLocalization.kernel_iff.{u + 1}
    (finiteTypeSheavesRestriction j) M
  rw [finiteTypeSheavesRestriction_kernel_eq_support] at h
  exact h

/-- The compatible support category is an actual small presentation of the
geometric supported coherent category. -/
def coherentGlobalSmallSupportEquivalence :
    (coherentGlobalSmallSupport j).FullSubcategory ≌
      SupportedFiniteTypeSheaves j :=
  (equivSmallModel.{u + 1} (FiniteTypeSheaves X)).symm.congrFullSubcategory (by
    funext M
    apply propext
    exact (coherentGlobalSmallSupport_iff j M).symm)

/-- This actual small support presentation commutes with the original
geometric inclusion of supported coherent sheaves. -/
theorem coherentGlobalSmallSupportEquivalence_comp_inclusion :
    (coherentGlobalSmallSupportEquivalence j).functor ⋙ (finiteTypeSheavesSupportedAway j).ι =
      (coherentGlobalSmallSupport j).ι ⋙
        (equivSmallModel.{u + 1} (FiniteTypeSheaves X)).inverse := rfl

/-- The genuine exact inclusion of actual supported coherent sheaves. -/
def supportedCoherentInclusionExact :
    ExactFunctor (supportedCoherentExactStructure j) (coherentExactStructure X) :=
  Devissage.exactInclusion (finiteTypeSheavesSupportedAway j)

/-- The compatible support category is abelian under the actual noetherian
hypotheses, using its Serre-class closure properties. -/
instance instAbelianCoherentGlobalSmallSupport :
    Abelian (coherentGlobalSmallSupport j).FullSubcategory :=
  Devissage.subcategoryAbelian (coherentGlobalSmallSupport j)

/-- The compatible supported K-term in the upper universe. -/
abbrev CoherentGlobalSupportedG (n : ℕ) : Type (u + 1) :=
  (abelianExactStructure (coherentGlobalSmallSupport j).FullSubcategory).K n

/-- The comparison between the two actual small support presentations. -/
def coherentGlobalSupportSmallModelEquivalence :
    SmallModel.{u + 1} (SupportedFiniteTypeSheaves j) ≌
      (coherentGlobalSmallSupport j).FullSubcategory :=
  (equivSmallModel.{u + 1} (SupportedFiniteTypeSheaves j)).symm.trans
    (coherentGlobalSmallSupportEquivalence j).symm

instance coherentGlobalSupportSmallModelEquivalence_additive :
    (coherentGlobalSupportSmallModelEquivalence j).functor.Additive := by
  let := preservesBinaryBiproducts_of_preservesBinaryProducts
    (coherentGlobalSupportSmallModelEquivalence j).functor
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- The exact comparison of support presentations. -/
def coherentGlobalSupportComparison :
    ExactFunctor (supportedCoherentExactStructure j).smallModel
      (abelianExactStructure (coherentGlobalSmallSupport j).FullSubcategory) where
  toFunctor := (coherentGlobalSupportSmallModelEquivalence j).functor
  map_conflation S h := by
    change (abelianExactStructure (SupportedFiniteTypeSheaves j)).smallModel.conflation S at h
    rw [abelianExactStructure_smallModel] at h
    exact h.map_of_exact _

/-- The comparison square is the actual support inclusion square, already
at the level of exact functors, before applying K-theory. -/
theorem coherentGlobalSupportComparison_comp_inclusion :
    (coherentGlobalSupportComparison j).comp
        (Devissage.exactInclusion (coherentGlobalSmallSupport j)) =
      (supportedCoherentInclusionExact j).smallModel.comp
        (SmallModelLocalization.standardExactFunctor.{u + 1} (FiniteTypeSheaves X)) := rfl

instance coherentGlobalSupportComparison_isEquivalence :
    (coherentGlobalSupportComparison j).toFunctor.IsEquivalence :=
  (coherentGlobalSupportSmallModelEquivalence j).isEquivalence_functor

instance coherentGlobalSupportComparison_mapQ_isEquivalence :
    (coherentGlobalSupportComparison j).mapQ.IsEquivalence := by
  apply ExactFunctor.mapQ_isEquivalence_of_equivalence
  · intro M N f hf
    change (abelianExactStructure (SupportedFiniteTypeSheaves j)).smallModel.inflation f
    rw [abelianExactStructure_smallModel, abelianExactStructure_inflation_iff]
    exact (coherentGlobalSupportComparison j).toFunctor.mono_of_mono_map
      ((abelianExactStructure_inflation_iff _ _).mp hf)
  · intro M N f hf
    change (abelianExactStructure (SupportedFiniteTypeSheaves j)).smallModel.deflation f
    rw [abelianExactStructure_smallModel, abelianExactStructure_deflation_iff]
    exact (coherentGlobalSupportComparison j).toFunctor.epi_of_epi_map
      ((abelianExactStructure_deflation_iff _ _).mp hf)

/-- The public actual supported G-group agrees with the compatible support
term of the localization theorem, in the same universe. -/
def coherentGlobalSupportedGEquiv (n : ℕ) :
    SupportedG j n ≃* CoherentGlobalSupportedG j n :=
  (coherentGlobalSupportComparison j).KEquivOfMapQIsEquivalence n

end Quillen.CoherentScheme
