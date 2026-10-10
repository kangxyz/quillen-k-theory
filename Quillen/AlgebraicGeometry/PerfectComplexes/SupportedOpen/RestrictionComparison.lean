/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.SupportedOpen.Restriction
public import Quillen.AlgebraicGeometry.PerfectComplexes.PairPullback

/-!
# Supported restriction is the original public pair pullback

The literal inverse-image open square defines an actual morphism of the
existing open-pair category. Original restriction and geometric pullback are
naturally isomorphic on bounded-flat supported objects. Through their actual
inclusion equivalences, the exact supported restriction K-map is precisely
the existing public perfectSupportedKPullback in every connective degree.
Only compactness of the two ambient schemes is needed for this last equality;
no quasi-separatedness or compactness of the auxiliary support open is used.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens)

/-- The original support open, viewed as an actual open-pair object. -/
def supportOpenPair : Quillen.Scheme.OpenPairs.{u} :=
  ⟨Arrow.mk T.ι, (by change IsOpenImmersion T.ι; infer_instance)⟩

/-- The literal inverse-image support square. -/
def supportRestrictionPair : supportOpenPair (j ⁻¹ᵁ T) ⟶ supportOpenPair T :=
  ObjectProperty.homMk (Arrow.homMk (j.resLE T (j ⁻¹ᵁ T) le_rfl) j
    (j.resLE_comp_ι le_rfl))

/-- Restriction and pullback agree through the original supported inclusions. -/
def boundedFlatPerfectSupportedOriginalRestrictionIso :
    boundedFlatPerfectSupportedInclusion T.ι ⋙ perfectSupportedRestrict j T ≅
      boundedFlatPerfectSupportedPullback (supportRestrictionPair j T) ⋙
        boundedFlatPerfectSupportedInclusion (j ⁻¹ᵁ T).ι :=
  Functor.fullyFaithfulCancelRight (perfectSupported (j ⁻¹ᵁ T).ι).ι
    (Functor.isoWhiskerLeft (boundedFlatPerfectSupported T.ι).ι
      (restrictIsoPullbackComplex j))

lemma perfectSupportedKRestrict_comp_boundedFlat (n : ℕ) :
    (perfectSupportedKRestrict j T n).comp
        (boundedFlatPerfectSupportedToPerfectSupportedKMap T.ι n) =
      (boundedFlatPerfectSupportedToPerfectSupportedKMap (j ⁻¹ᵁ T).ι n).comp
        (boundedFlatPerfectSupportedKPullback (supportRestrictionPair j T) n) := by
  unfold perfectSupportedKRestrict boundedFlatPerfectSupportedToPerfectSupportedKMap
    boundedFlatPerfectSupportedKPullback
  rw [← Waldhausen.KMap_comp, ← Waldhausen.KMap_comp]
  exact Waldhausen.KMap_eq_of_iso _ _
    (boundedFlatPerfectSupportedOriginalRestrictionIso j T) n

variable [CompactSpace X] [CompactSpace U]

/-- The same original square in the existing qc open-pair category. -/
def qcSupportRestrictionPair :
    (⟨supportOpenPair (j ⁻¹ᵁ T), (by change CompactSpace U; infer_instance)⟩ :
      Quillen.Scheme.QuasiCompactOpenPairs.{u}) ⟶
      ⟨supportOpenPair T, (by change CompactSpace X; infer_instance)⟩ :=
  ObjectProperty.homMk (supportRestrictionPair j T)

/-- The literal exact restriction map is the existing public supported pullback. -/
lemma perfectSupportedKRestrict_eq_pullback (n : ℕ) :
    perfectSupportedKRestrict j T n = perfectSupportedKPullback (qcSupportRestrictionPair j T) n :=
      by
  exact perfectSupportedKPullback_unique (qcSupportRestrictionPair j T) n
    (perfectSupportedKRestrict j T n) (perfectSupportedKRestrict_comp_boundedFlat j T n)

end Quillen.PerfectComplexes
