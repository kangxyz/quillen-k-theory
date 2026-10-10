/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.PrincipalWeakImage

/-! # Original stabilized restriction-image consumers -/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
attribute [local instance] Abelian.hasFiniteBiproducts
namespace Quillen.Tests.PrincipalWeakImage
open PerfectComplexes OpenWeakImage

/-- Membership produces an actual original perfect restriction arrow, without App2. -/
theorem original_stabilized_restriction_arrow (R : CommRingCat.{u}) (r : R)
    (P : StrictPerfect (Spec (.of (Localization.Away r)))) :
    ∃ (E : Perfect (Spec R))
      (q : (perfectRestrict (CoherentScheme.principalOpen R r)).obj E ⟶
        shiftSum ((strictToPerfect _).obj P)), (perfectWaldhausen _).weq q :=
  principal_strict_shiftSum_mem R r P

/-- A given weak strict comparison supplies stabilized membership for the actual target itself. -/
theorem actual_target_stabilized_comparison (R : CommRingCat.{u}) (r : R)
    (B : Perfect (Spec (.of (Localization.Away r))))
    (P : StrictPerfect (Spec (.of (Localization.Away r))))
    (f : (strictToPerfect _).obj P ⟶ B) (hf : (perfectWaldhausen _).weq f) :
    ∃ (E : Perfect (Spec R))
      (q : (perfectRestrict (CoherentScheme.principalOpen R r)).obj E ⟶ shiftSum B),
      (perfectWaldhausen _).weq q := principal_shiftSum_mem_of_strict_comparison R r B P f hf

/-- The stabilization comparison retains its original first-component map exactly. -/
theorem actual_first_projection {X : Scheme.{u}} {P Q : Perfect X} (f : P ⟶ Q) :
    (shiftSumMap f).hom ≫ biprod.fst = biprod.fst ≫ f.hom := biprod.map_fst _ _

end Quillen.Tests.PrincipalWeakImage
