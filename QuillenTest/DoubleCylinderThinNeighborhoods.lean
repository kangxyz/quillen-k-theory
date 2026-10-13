/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.DoubleMappingCylinder.ThinNeighborhoods

/-! # Actual collar and nonconstant-endpoint-track tests for ambient thinness -/
@[expose] public section
noncomputable section
open CategoryTheory Limits MonoidalCategory
open scoped unitInterval
universe u
namespace QuillenTest.DoubleCylinderThinNeighborhoods
open Quillen

/-- A homotopy with genuinely moving endpoint tracks. -/
def movingTrackHomotopy :
    (ContinuousMap.const ℝ (0 : ℝ)).Homotopy (ContinuousMap.id ℝ) where
  toFun p := (p.1 : ℝ) * p.2
  continuous_toFun := by fun_prop
  map_zero_left x := by simp
  map_one_left x := by simp

/-- The test homotopy does not fix its endpoint at one. -/
theorem endpoint_track_moves : movingTrackHomotopy (0, 1) ≠ movingTrackHomotopy (1, 1) := by
  norm_num [movingTrackHomotopy]

/-- Cancellation is applied to that nonconstant-track homotopy, not a based substitute. -/
theorem moving_track_cancellation {x y : ℝ} (p q : Path x y) : p.Homotopic q := by
  have h : (p.map (ContinuousMap.const ℝ (0 : ℝ)).continuous).Homotopic
      (q.map (ContinuousMap.const ℝ (0 : ℝ)).continuous) :=
    Path.Homotopic.refl (Path.refl 0)
  have hh := path_map_homotopic_of_homotopy movingTrackHomotopy p q h
  change (p.map continuous_id).Homotopic (q.map continuous_id) at hh
  simpa only [Path.map_id] using hh

variable {A B C D : TopCat.{u}} (f : A ⟶ B) (g : A ⟶ C)
  {l : A ⊗ TopCat.I ⟶ D} {e : TopCat.of (B ⊕ C) ⟶ D}
  (sq : IsPushout (Quillen.intervalEndpoints A) (DoubleCylinder.endMap f g) l e)

include sq in
/-- The original left endpoint is covered, for arbitrary possibly noninjective attachments. -/
theorem original_left_endpoint (EB : PathThinNeighborhoods B) (cut : unitInterval)
    (hcut : 0 < cut) (b : B) :
    ∃ V : Set D, IsOpen V ∧ e (Sum.inl b) ∈ V ∧ AmbientPathThin V :=
  DoubleCylinder.leftCollar_exists_open_ambientPathThin f g sq EB cut hcut
    (DoubleCylinder.leftCollarInclusion f g sq cut hcut b)

include sq in
/-- The original right endpoint is covered with the same actual quotient map. -/
theorem original_right_endpoint (EC : PathThinNeighborhoods C) (cut : unitInterval)
    (hcut : cut < 1) (c : C) :
    ∃ V : Set D, IsOpen V ∧ e (Sum.inr c) ∈ V ∧ AmbientPathThin V :=
  DoubleCylinder.rightCollar_exists_open_ambientPathThin f g sq EC cut hcut
    (DoubleCylinder.rightCollarInclusion f g sq cut hcut c)

include sq in
/-- No LPC instance is assumed on the double-cylinder target. -/
theorem original_quotient_lpc [LocallyPathConnectedSpace A]
    [LocallyPathConnectedSpace B] [LocallyPathConnectedSpace C] :
    LocallyPathConnectedSpace D := DoubleCylinder.locallyPathConnectedSpace f g sq

include sq in
/-- The whole double cylinder receives an actual thin-neighborhood structure. -/
theorem original_thin_structure [LocallyPathConnectedSpace A]
    [LocallyPathConnectedSpace B] [LocallyPathConnectedSpace C]
    (EB : PathThinNeighborhoods B) (EC : PathThinNeighborhoods C) :
    Nonempty (PathThinNeighborhoods D) := ⟨DoubleCylinder.pathThinNeighborhoods f g sq EB EC⟩

end QuillenTest.DoubleCylinderThinNeighborhoods
