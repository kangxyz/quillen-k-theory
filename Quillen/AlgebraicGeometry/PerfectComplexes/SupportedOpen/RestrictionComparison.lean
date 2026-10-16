/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.SupportedRestriction


public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Support.Pairs


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

lemma perfectSupportedKRestrict_comp_boundedFlat (n : ℕ) :
    (perfectSupportedKRestrict j T n).comp
        (boundedFlatPerfectSupportedToPerfectSupportedKMap T.ι n) =
      (boundedFlatPerfectSupportedToPerfectSupportedKMap (j ⁻¹ᵁ T).ι n).comp
        (boundedFlatPerfectSupportedKPullback (supportRestrictionPair j T) n) := by
  unfold perfectSupportedKRestrict boundedFlatPerfectSupportedToPerfectSupportedKMap
    boundedFlatPerfectSupportedKPullback
  rw [Waldhausen.KMap_comp_KMap, Waldhausen.KMap_comp_KMap]
  exact Waldhausen.KMap_eq_of_iso _ _
    (boundedFlatPerfectSupportedOriginalRestrictionIso j T) n

variable [CompactSpace X] [CompactSpace U]

/-- The literal exact restriction map is the existing public supported pullback. -/
lemma perfectSupportedKRestrict_eq_pullback (n : ℕ) :
    perfectSupportedKRestrict j T n = perfectSupportedKPullback (qcSupportRestrictionPair j T) n :=
      by
  exact perfectSupportedKPullback_unique (qcSupportRestrictionPair j T) n
    (perfectSupportedKRestrict j T n) (perfectSupportedKRestrict_comp_boundedFlat j T n)

end Quillen.PerfectComplexes
