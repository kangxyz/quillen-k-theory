/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.AlgebraicGeometry.Scheme.Coherent.ClosedImmersion.GeneralReflection
public import Quillen.AlgebraicGeometry.Scheme.Coherent.ClosedImmersion.IdealSupport
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Genuine closed support and its affine/open base-change identifications -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Quillen.CoherentScheme.ClosedImmersion.Ideal
variable (R : CommRingCat.{u}) (I : Ideal R)

/-- The actual quotient closed immersion has precisely the zero-locus image. -/
theorem closedMap_range : Set.range (closedMap R I) = PrimeSpectrum.zeroLocus (I : Set R) := by
  change Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I)) = _
  rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,
    Ideal.mk_ker]

end Quillen.CoherentScheme.ClosedImmersion.Ideal

namespace Quillen.CoherentScheme.ClosedImmersion.General
variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- The actual open complement of the closed immersion's underlying image. -/
def openComplement : X.Opens :=
  ⟨(Set.range i)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩

/-- The open immersion of the complement of the closed image of `i` into `X`. -/
def openMap : (openComplement i).toScheme ⟶ X := (openComplement i).ι
instance : IsOpenImmersion (openMap i) := by unfold openMap; infer_instance

@[simp] theorem openMap_range : Set.range (openMap i) = (Set.range i)ᶜ :=
  Scheme.Opens.range_ι _

variable [IsLocallyNoetherian X]

/-- Support on the actual closed image is precisely vanishing on its open complement. -/
theorem supported_iff (M : FiniteTypeSheaves X) :
    finiteTypeSheavesSupportedAway (openMap i) M ↔ SchemeSheaf.support M.obj ⊆ Set.range i := by
  rw [finiteTypeSheavesSupportedAway_iff_support_subset, openMap_range, compl_compl]

/-- Actual closed support pulls back to the actual closed image on every open chart. -/
theorem supported_restrict {V : Scheme.{u}} [IsLocallyNoetherian V]
    (a : V ⟶ X) [IsOpenImmersion a] (M : FiniteTypeSheaves X)
    (hM : finiteTypeSheavesSupportedAway (openMap i) M) :
    finiteTypeSheavesSupportedAway (openMap (pullback.snd i a)) ((finiteTypeSheavesRestriction a).obj M) := by
  rw [supported_iff, Scheme.Pullback.range_snd]
  change SchemeSheaf.support (M.obj.restrict a) ⊆ a ⁻¹' Set.range i
  rw [SchemeSheaf.support_restrict]
  exact Set.preimage_mono ((supported_iff i M).mp hM)

variable [IsLocallyNoetherian Z]

/-- The actual closed pushforward is supported on the genuine closed image. -/
theorem coherentPushforward_supported (M : FiniteTypeSheaves Z) :
    finiteTypeSheavesSupportedAway (openMap i) ((coherentPushforward i).obj M) := by
  have : IsEmpty (pullback i (openMap i) : Scheme) :=
    Scheme.isEmpty_pullback i (openMap i) (by rw [openMap_range]; exact disjoint_compl_right)
  have hz : IsZero ((Scheme.Modules.restrictFunctor (pullback.fst i (openMap i))).obj M.obj) := by
    apply (SchemeSheaf.isZero_iff_stalks _).mpr
    intro x
    exact isEmptyElim x
  have hz' := (Scheme.Modules.pushforward (pullback.snd i (openMap i))).map_isZero hz
  exact hz'.of_iso ((openBaseChange i (openMap i)).app M.obj)

/-- Every actual closed-image coherent object has genuine closed support. -/
theorem coherentKilled_le_supported : coherentKilled i ≤ finiteTypeSheavesSupportedAway (openMap i) := by
  rintro M ⟨N, ⟨e⟩⟩
  exact (finiteTypeSheavesSupportedAway (openMap i)).prop_of_iso e (coherentPushforward_supported i N)

end Quillen.CoherentScheme.ClosedImmersion.General
