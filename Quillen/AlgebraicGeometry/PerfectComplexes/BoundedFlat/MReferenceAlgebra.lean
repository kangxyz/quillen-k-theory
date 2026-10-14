/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MComponentReferences

/-! Small-functor forms of actual anchored normalized pullback coherence. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.BassMJoin
open BassReferenceMerge

/-- Actual anchored factorization coherence after the fixed small-category transport. -/
theorem small_anchored_factorization {X Y Z T : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)
    (d : X ⟶ Z) (w : X ⟶ T)
    (hd : d = f ≫ g) (hl : w = d ≫ h) (hr : w = f ≫ g ≫ h) :
    smallIso (eqToIso (congrArg boundedFlatNormalizedPullback hr) ≪≫
      boundedFlatNormalizedPullbackCompIso f (g ≫ h)) ≪≫
      isoWhiskerRight (smallIso (boundedFlatNormalizedPullbackCompIso g h))
        (AsSmall.down ⋙ boundedFlatNormalizedPullback f ⋙ AsSmall.up) =
    smallIso (eqToIso (congrArg boundedFlatNormalizedPullback hl) ≪≫
      boundedFlatNormalizedPullbackCompIso d h) ≪≫
      isoWhiskerLeft (AsSmall.down ⋙ boundedFlatNormalizedPullback h ⋙ AsSmall.up)
        (smallIso (eqToIso (congrArg boundedFlatNormalizedPullback hd) ≪≫
          boundedFlatNormalizedPullbackCompIso f g)) := by
  rw [smallIso_postcomp, smallIso_precomp, ← smallIso_trans, ← smallIso_trans]
  apply congrArg smallIso
  simpa only [eqToIso_refl, Iso.refl_trans, Iso.trans_assoc] using
    (anchored_factorizations_strict f g h d (g ≫ h) w hd rfl hl hr).symm

/-- A reflexive geometric endpoint transport retains the exact native binary reference. -/
theorem small_binary_refl {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : f ≫ g = f ≫ g) :
    smallIso (boundedFlatNormalizedPullbackCompIso f g) =
      smallIso (eqToIso (congrArg boundedFlatNormalizedPullback h) ≪≫
        boundedFlatNormalizedPullbackCompIso f g) := by
  rw [eqToIso_refl, Iso.refl_trans]

/-- A geometric source equality retains its full original binary endpoint reference. -/
theorem small_binary_transport {X Y Z : Scheme.{u}} (d : X ⟶ Z)
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : d = f ≫ g) :
    eqToIso (congrArg (fun F ↦ AsSmall.down ⋙ F ⋙ AsSmall.up)
      (congrArg boundedFlatNormalizedPullback h)) ≪≫
      smallIso (boundedFlatNormalizedPullbackCompIso f g) =
    smallIso (eqToIso (congrArg boundedFlatNormalizedPullback h) ≪≫
      boundedFlatNormalizedPullbackCompIso f g) := by
  rw [smallIso_trans, smallIso_eqToIso]

end Quillen.PerfectComplexes.BassMJoin
