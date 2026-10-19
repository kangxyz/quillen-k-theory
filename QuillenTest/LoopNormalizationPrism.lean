/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Topology.HomotopyGroups.Loop.NormalizationPrismRelative

/-!
# Parameter and based-map regressions for the complete normalization prism

The transformed data below are constructed from actual maps, rather than supplied with a
postulated prism square. The test retains independent prism, self-track, and row coordinates.
-/
@[expose] public section
noncomputable section
open scoped Topology unitInterval
universe u v w z
open Quillen Quillen.LoopNormalizationPrism
namespace QuillenTest.LoopNormalizationPrism
variable {X : Type u} {X' : Type v} {Y : Type w} {Y' : Type z}
  [TopologicalSpace X] [TopologicalSpace X'] [TopologicalSpace Y] [TopologicalSpace Y']
  {y : Y} {y' : Y'}
variable (f : C(Y, Y')) (hf : f y = y') (k : C(X', X))
  (γ : C(X, Path y y)) (α : γ.Homotopy γ)
  (N : γ.Homotopy (ContinuousMap.const X (Path.refl y)))

/-- The component family under actual input reindexing and based postcomposition. -/
def mappedComponent : C(X', Path y' y') := (basedLoopMap f hf).comp (γ.comp k)

/-- The complete original self-track under the same actual maps. -/
def mappedTrack : (mappedComponent f hf k γ).Homotopy (mappedComponent f hf k γ) where
  toFun z := basedLoopMap f hf (α (z.1, k z.2))
  continuous_toFun := (basedLoopMap f hf).continuous.comp
    (α.continuous.comp (continuous_fst.prodMk (k.continuous.comp continuous_snd)))
  map_zero_left x := by simp [mappedComponent]
  map_one_left x := by simp [mappedComponent]

/-- The complete supplied null under the same actual maps. -/
def mappedNull : (mappedComponent f hf k γ).Homotopy
    (ContinuousMap.const X' (Path.refl y')) where
  toFun z := basedLoopMap f hf (N (z.1, k z.2))
  continuous_toFun := (basedLoopMap f hf).continuous.comp
    (N.continuous.comp (continuous_fst.prodMk (k.continuous.comp continuous_snd)))
  map_zero_left x := by simp [mappedComponent]
  map_one_left x := by simp [basedLoopMap_refl]

/-- Actual continuous maps preserve the entire three-time prism at every residual input. -/
theorem actual_maps (r t s : unitInterval) (x : X') :
    f (normalizationHomotopy γ α N (r, k x) t s) =
      normalizationHomotopy (mappedComponent f hf k γ) (mappedTrack f hf k γ α)
        (mappedNull f hf k γ N) (r, x) t s := by
  exact congrArg (fun p : Path (Path.refl y') (Path.refl y') ↦ p t s)
    (normalizationHomotopy_naturality f hf k γ α N
      (mappedComponent f hf k γ) (mappedTrack f hf k γ α) (mappedNull f hf k γ N)
      (fun _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) r x)

/-- The original null-conjugation word keeps its self-track and row times separate. -/
theorem original_end_word (x : X) (t s : unitInterval) :
    normalizationHomotopy γ α N (1, x) t s =
      ((N.evalAt x).symm.trans ((α.evalAt x).trans (N.evalAt x))) t s :=
  congrArg (fun p : Path (Path.refl y) (Path.refl y) ↦ p t s)
    (normalizationHomotopy_one γ α N x)

/-- The original inverse-prefix cancellation is retained at the other end. -/
theorem original_normalization (x : X) (t s : unitInterval) :
    normalizationHomotopy γ α N (0, x) t s =
      loopNormalizedSelfTrack (γ x) (α.evalAt x) t s :=
  congrArg (fun p : Path (Path.refl y) (Path.refl y) ↦ p t s)
    (normalizationHomotopy_zero γ α N x)

/-- A genuine constant input is fixed for every one of the three independent times. -/
theorem constant_input (x : X) (hγ : γ x = Path.refl y)
    (hα : ∀ t, α (t, x) = Path.refl y) (hN : ∀ t, N (t, x) = Path.refl y)
    (r t s : unitInterval) : normalizationHomotopy γ α N (r, x) t s = y :=
  congrArg (fun p : Path (Path.refl y) (Path.refl y) ↦ p t s)
    (normalizationHomotopy_fixed γ α N x hγ hα hN r)

end QuillenTest.LoopNormalizationPrism
