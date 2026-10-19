/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.RowLoopPrespectrum
public import Quillen.Topology.HomotopyGroups.Loop.NormalizationPrismFaces
public import Quillen.Topology.HomotopyGroups.Loop.NormalizedSelfTrackNaturality

/-!
# Original inverse-prefix normalization in the distinguished-row spectrum

The standard loop normalization is applied to an actual self-track with target the genuine
row-loop prespectrum. Its positive-level structure square follows from the actual based-map
row structure, preserving the original cancellation path. Degree zero is the loop extension of
the positive operation with its explicit parameter transpose. This constructs a whole spectrum
map and does not replace the separate comparison with a specified cofiber null.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Quillen.Waldhausen.IteratedS
variable {V W : Model.{u}} (f : prespectrum V ⟶ rowLoopPrespectrum W)
  (H : LoopPrespectrum.Homotopy f f)

/-- Normalize the complete positive self-track using the original inverse-prefix cancellation. -/
def rowSelfTrackStage (k : ℕ) :
    C(stageSpace k V,
      Path (Path.refl (stagePoint (k + 1) W)) (Path.refl (stagePoint (k + 1) W))) :=
  LoopNormalizationPrism.normalized (f.map (k + 1)) (H.levelHomotopy (k + 1)).toHomotopy

/-- The normalization retains the original actual loop, self-track and cancellation word. -/
theorem rowSelfTrackStage_apply (k : ℕ) (x : stageSpace k V) :
    rowSelfTrackStage f H k x = loopNormalizedSelfTrack (f.map (k + 1) x)
      ((H.levelHomotopy (k + 1)).toHomotopy.evalAt x) :=
  LoopNormalizationPrism.normalized_apply _ _ x

/-- Every positive normalized operation preserves the actual source point. -/
theorem rowSelfTrackStage_point (k : ℕ) :
    rowSelfTrackStage f H k (stagePoint k V) =
      Path.refl (Path.refl (stagePoint (k + 1) W)) := by
  rw [rowSelfTrackStage_apply]
  apply Path.ext
  funext t
  apply Path.ext
  funext s
  exact loopNormalizedSelfTrack_pointwise id (fun _ : Unit => stagePoint (k + 1) W)
    (f.map (k + 1) (stagePoint k V)) (Path.refl ())
    ((H.levelHomotopy (k + 1)).toHomotopy.evalAt (stagePoint k V))
    (Path.refl (Path.refl ()))
    (fun a => congrArg (fun p : Path (stagePoint (k + 1) W) (stagePoint (k + 1) W) => p a)
      (f.map_point (k + 1)))
    (fun b a => congrArg (fun p : Path (stagePoint (k + 1) W) (stagePoint (k + 1) W) => p a)
      (H.at_point (k + 1) b)) t s

/-- The full positive structure square keeps the normalization and row times unchanged. -/
theorem rowSelfTrackStage_structure (k : ℕ) (x : stageSpace k V)
    (r t s : unitInterval) :
    rowLoopStructureEvaluation k W r (rowSelfTrackStage f H k x t s) =
      rowSelfTrackStage f H (k + 1) (stageLoopMap k V x r) t s := by
  rw [rowSelfTrackStage_apply, rowSelfTrackStage_apply]
  apply loopNormalizedSelfTrack_pointwise (rowLoopStructureEvaluation k W r) id
  · intro a
    have hf := congrArg (fun p => p r) (f.comm (k + 1) x)
    exact (congrArg (fun p : Path (stagePoint (k + 2) W) (stagePoint (k + 2) W) => p a) hf).symm
  · intro b a
    exact (congrArg (fun p : Path (stagePoint (k + 2) W) (stagePoint (k + 2) W) => p a)
      (H.comm (k + 1) b x r)).symm

/-- The complete normalized operation, with its explicit zero-level parameter transpose. -/
def rowSelfTrackOperation : prespectrum V ⟶ LoopPrespectrum.parameterLooping
    (rowLoopPrespectrum W) where
  map n := Nat.casesOn n
    ((doubleLoopTranspose (Path.refl (stagePoint 1 W))).comp
      (basedLoopMap (rowSelfTrackStage f H 0) (rowSelfTrackStage_point f H 0)))
    (rowSelfTrackStage f H)
  map_point n := by
    cases n with
    | zero =>
      change doubleLoopTranspose _ (basedLoopMap _ _ (Path.refl _)) = _
      rw [basedLoopMap_refl, doubleLoopTranspose_refl]
      rfl
    | succ k => exact rowSelfTrackStage_point f H k
  comm n x := by
    cases n with
    | zero =>
      apply Path.ext
      funext r
      apply Path.ext
      funext t
      rfl
    | succ k =>
      apply Path.ext
      funext r
      apply Path.ext
      funext t
      apply Path.ext
      funext s
      exact (rowSelfTrackStage_structure f H k x r t s).symm

/-- Positive levels are the literal original normalized first-row self-tracks. -/
theorem rowSelfTrackOperation_succ (k : ℕ) (x : stageSpace k V) :
    (rowSelfTrackOperation f H).map (k + 1) x = rowSelfTrackStage f H k x := rfl

/-- Degree zero displays the forward unit time before the independent original input-loop time. -/
theorem rowSelfTrackOperation_zero (γ : Path (stagePoint 0 V) (stagePoint 0 V))
    (t a s : unitInterval) :
    Path.toContinuousMap (Path.toContinuousMap
      (Path.toContinuousMap ((rowSelfTrackOperation f H).map 0 γ) t) a) s =
        rowSelfTrackStage f H 0 (γ a) t s := rfl

end Quillen.Waldhausen.IteratedS
