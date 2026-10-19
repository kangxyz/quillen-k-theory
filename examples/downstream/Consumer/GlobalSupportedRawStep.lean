/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalSupportedRawStep
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalSupportedRawRows

/-! Independent uses of the actual three supported first stages and their original tracks. -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
open Quillen.PerfectComplexes.GlobalSupportedRawBass
universe u
namespace Consumer.GlobalSupportedRawStep

/-- All three localization rows have actual objectwise supported raw first-stage seeds. -/
def threeRowSeeds {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    [CompactSpace U] [CompactSpace X] (T : X.Opens) :
    (rawSpectrum (Rows.source j T).obj ⟶ step (Rows.source j T)) ×
      (rawSpectrum (Rows.middle T).obj ⟶ step (Rows.middle T)) ×
        (rawSpectrum (Rows.target j T).obj ⟶ step (Rows.target j T)) :=
  ⟨transition _, transition _, transition _⟩

/-- The target seed retains the original full unit/null word at every loop coordinate. -/
theorem target_seed_word {U X : Scheme.{u}} (j : U ⟶ X) [CompactSpace U]
    (T : X.Opens) (n : ℕ) (x : (rawSpectrum (Rows.target j T).obj).space n)
    (s : unitInterval) :
    Path.toContinuousMap ((transition (Rows.target j T)).map n x) s =
      (((unitHomotopy (Rows.target j T)).postcomp
        (mappingConeInclusion (comparison (Rows.target j T)))).conjugateToZero
        (sourceNull (Rows.target j T))).level n (s, x) :=
  transition_apply _ n x s

/-- Relative split recovery preserves the independent prespectrum structure coordinate. -/
theorem middle_triangle_structure {X : Scheme.{u}} [CompactSpace X] (T : X.Opens)
    (n : ℕ) (r s t : unitInterval) (x : (rawSpectrum (Rows.middle T).obj).space n) :
    (plusComparison (Rows.middle T)).level (n + 1)
        (r, (s, (rawSpectrum (Rows.middle T).obj).structureMap n x t)) =
      (rawSpectrum (Geometry.laurent (Rows.middle T))).structureMap n
        ((plusComparison (Rows.middle T)).level n (r, (s, x))) t :=
  (plusComparison (Rows.middle T)).comm n r s x t

end Consumer.GlobalSupportedRawStep
