/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.RowLoopFunctor
public import Quillen.Waldhausen.SConstruction.Iterated.RowSwapTransformation
public import Quillen.Waldhausen.SConstruction.Iterated.PrespectrumHomotopy
public import Quillen.Topology.Prespectrum.HomotopyTransport

/-!
# Original weak-transformation tracks on the distinguished-row prespectrum

The original weak-transformation homotopy acts pointwise on the distinguished row loop.
Its complete spectrum structure square uses the genuine row-transpose identity, rather than
ordinary-loop naturality. The actual row-stabilization comparison preserves each entire track,
including its zero-level loop extension and the specified endpoint identifications.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Quillen.Waldhausen.IteratedS
variable {V W : Model.{u}} {F G : V ⟶ W}
  (η : F.functor ⟶ G.functor) (hη : ∀ A, W.waldhausen.weq (η.app A))

/-- The original transformation acts on every point of the whole coefficient row loop. -/
def rowLoopStageHomotopy (k : ℕ) :
    C(unitInterval × Path (stagePoint (k + 1) V) (stagePoint (k + 1) V),
      Path (stagePoint (k + 1) W) (stagePoint (k + 1) W)) where
  toFun z := {
    toFun s := stageTransformationTopHomotopy (k + 1) η hη (z.1, z.2 s)
    continuous_toFun := by fun_prop
    source' := by
      rw [Path.source]
      exact stageTransformationTopHomotopy_fixed_point (k + 1) η hη z.1
    target' := by
      rw [Path.target]
      exact stageTransformationTopHomotopy_fixed_point (k + 1) η hη z.1 }
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    change Continuous (fun z : (unitInterval ×
      Path (stagePoint (k + 1) V) (stagePoint (k + 1) V)) × unitInterval =>
        stageTransformationTopHomotopy (k + 1) η hη (z.1.1, z.1.2 z.2))
    fun_prop

/-- The entire constant coefficient row is fixed by the transformation. -/
theorem rowLoopStageHomotopy_point (k : ℕ) (t : unitInterval) :
    rowLoopStageHomotopy η hη k (t, Path.refl (stagePoint (k + 1) V)) =
      Path.refl (stagePoint (k + 1) W) := by
  apply Path.ext
  funext s
  exact stageTransformationTopHomotopy_fixed_point (k + 1) η hη t

/-- The actual zero-level extension of the positive row-loop track. -/
def rowLoopZeroHomotopy :
    C(unitInterval × Path (Path.refl (stagePoint 1 V)) (Path.refl (stagePoint 1 V)),
      Path (Path.refl (stagePoint 1 W)) (Path.refl (stagePoint 1 W))) where
  toFun z := {
    toFun s := rowLoopStageHomotopy η hη 0 (z.1, z.2 s)
    continuous_toFun := by fun_prop
    source' := by
      rw [Path.source]
      exact rowLoopStageHomotopy_point η hη 0 z.1
    target' := by
      rw [Path.target]
      exact rowLoopStageHomotopy_point η hη 0 z.1 }
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    change Continuous (fun z : (unitInterval ×
      Path (Path.refl (stagePoint 1 V)) (Path.refl (stagePoint 1 V))) × unitInterval =>
        rowLoopStageHomotopy η hη 0 (z.1.1, z.1.2 z.2))
    fun_prop

/-- A genuine weak transformation gives the whole distinguished-row prespectrum homotopy. -/
def rowLoopTransformationHomotopy :
    LoopPrespectrum.Homotopy (rowLoopMap F) (rowLoopMap G) where
  level n := Nat.casesOn n (rowLoopZeroHomotopy η hη) (rowLoopStageHomotopy η hη)
  at_zero n x := by
    cases n with
    | zero =>
      change Path (Path.refl _) (Path.refl _) at x
      apply Path.ext
      funext r
      apply Path.ext
      funext s
      exact (stageTransformationTopHomotopy 1 η hη).apply_zero (x r s)
    | succ k =>
      change Path _ _ at x
      apply Path.ext
      funext s
      exact (stageTransformationTopHomotopy (k + 1) η hη).apply_zero (x s)
  at_one n x := by
    cases n with
    | zero =>
      change Path (Path.refl _) (Path.refl _) at x
      apply Path.ext
      funext r
      apply Path.ext
      funext s
      exact (stageTransformationTopHomotopy 1 η hη).apply_one (x r s)
    | succ k =>
      change Path _ _ at x
      apply Path.ext
      funext s
      exact (stageTransformationTopHomotopy (k + 1) η hη).apply_one (x s)
  at_point n t := by
    cases n with
    | zero =>
      apply Path.ext
      funext r
      exact rowLoopStageHomotopy_point η hη 0 t
    | succ k => exact rowLoopStageHomotopy_point η hη k t
  comm n t x r := by
    cases n with
    | zero => rfl
    | succ k =>
      change Path _ _ at x
      apply Path.ext
      funext s
      change stageTransformationTopHomotopy (k + 2) η hη
        (t, stageRowSwapHomeomorph k V (stageLoopMap (k + 1) V (x s) r)) =
          stageRowSwapHomeomorph k W (stageLoopMap (k + 1) W
            (stageTransformationTopHomotopy (k + 1) η hη (t, x s)) r)
      rw [← stageTransformationTopHomotopy_rowSwap,
        stageTransformationTopHomotopy_structure]

/-- The row comparison preserves the whole original transformation track, not just its ends. -/
theorem rowStabilizationMap_transformation :
    ((prespectrumTransformationHomotopy η hη).postcomp (rowStabilizationMap W)).cast
        (rowStabilizationMap_naturality F) (rowStabilizationMap_naturality G) =
      (rowLoopTransformationHomotopy η hη).precomp (rowStabilizationMap V) := by
  apply LoopPrespectrum.Homotopy.ext
  funext n
  apply ContinuousMap.ext
  intro z
  cases n with
  | zero =>
    change unitInterval × Path (stagePoint 0 V) (stagePoint 0 V) at z
    apply Path.ext
    funext r
    apply Path.ext
    funext s
    exact (stageTransformationTopHomotopy_structure 0 η hη z.1 s (z.2 r)).symm
  | succ k =>
    apply Path.ext
    funext s
    exact (stageTransformationTopHomotopy_structure k η hη z.1 s z.2).symm

end Quillen.Waldhausen.IteratedS
