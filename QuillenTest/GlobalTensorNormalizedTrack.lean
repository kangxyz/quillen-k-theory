/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalTensorNormalizedTrack
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalTensorNormalizedSupport

/-! Whole tensor normalization and independent Bass-stage/track-time regression. -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.PerfectComplexes Quillen.KTheory.Bass
open Quillen.PerfectComplexes.GlobalTensorNormalizedTrack
universe u
namespace QuillenTest.GlobalTensorNormalizedTrack

/-- Every actual finite stage preserves the whole same-time map, not only a stable class. -/
theorem original_stage_time (i : ℕ) (X : Scheme.{u}ᵒᵖ) (r : unitInterval) :
    ((SchemeNaturalSeed.stageTrack tensorTrack i).homotopy X).at r =
      ((SchemeNaturalSeed.stageTrack scalarTrack i).homotopy X).at r := by
  rw [stageTrack_eq]

/-- The full raw identity automorphism retains the genuine tensor-unitor conjugate. -/
theorem original_tensor_word (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ) :
    (boundedFlatPerfectTensorUnitIso X).symm ≪≫
        boundedFlatPerfectTensorUnitAutomorphism X r ≪≫ boundedFlatPerfectTensorUnitIso X =
      boundedFlatPerfectGlobalUnitIso X r :=
  GlobalSectionChangeIndex.normalizedTensorUnit_eq X r

end QuillenTest.GlobalTensorNormalizedTrack
