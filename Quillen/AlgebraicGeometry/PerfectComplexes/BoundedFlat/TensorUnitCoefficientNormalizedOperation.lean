/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitCoefficientRowSpectrum
public import Quillen.Waldhausen.SConstruction.Iterated.RowSelfTrackOperation

/-!
# The actual normalized first-coefficient tensor operation

The independently realized tensor first-row cell, with its forward unit edge, is normalized by
the original inverse-prefix cancellation. The genuine row-compatible target makes this a whole
prespectrum map. The positive formulas display the original cell path, and degree zero retains
the separate unit, input-loop and coefficient-row times. Comparison with the prescribed Bass
cofiber null is a subsequent whole-homotopy statement, not a consequence of a K-one class equality.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (r : (Γ(X, ⊤))ˣ)

/-- The actual forward edge of the realized first coefficient row, before normalization. -/
def tensorUnitPullbackCoefficientStagePath (k : ℕ) (x : stageSpace k
    (modelOf (boundedFlatPerfectWaldhausen Y))) :
    Path
      ((boundedFlatPerfectTensorUnitPrespectrumMap f ≫
        rowStabilizationMap (modelOf (boundedFlatPerfectWaldhausen X))).map (k + 1) x)
      ((boundedFlatPerfectTensorUnitPrespectrumMap f ≫
        rowStabilizationMap (modelOf (boundedFlatPerfectWaldhausen X))).map (k + 1) x) where
  toFun t := tensorUnitPullbackCoefficientStageLoop f r k (t, x)
  continuous_toFun := by fun_prop
  source' := (tensorUnitPullbackCoefficientRowSpectrumHomotopy f r).at_zero (k + 1) x
  target' := (tensorUnitPullbackCoefficientRowSpectrumHomotopy f r).at_one (k + 1) x

/-- The two actual first-coefficient times remain in their original order. -/
theorem tensorUnitPullbackCoefficientStagePath_apply (k : ℕ)
    (x : stageSpace k (modelOf (boundedFlatPerfectWaldhausen Y))) (t s : unitInterval) :
    Path.toContinuousMap (tensorUnitPullbackCoefficientStagePath f r k x t) s =
      tensorUnitPullbackCoefficientStageRealization f r k (s, (t, x)) := rfl

/-- The entire realized cell path is the actual whole row-spectrum self-track at this input. -/
theorem tensorUnitPullbackCoefficientStagePath_eq (k : ℕ)
    (x : stageSpace k (modelOf (boundedFlatPerfectWaldhausen Y))) :
    tensorUnitPullbackCoefficientStagePath f r k x =
      ((tensorUnitPullbackCoefficientRowSpectrumHomotopy f r).levelHomotopy
        (k + 1)).toHomotopy.evalAt x := rfl

/-- Normalize the independently realized first-coefficient cells into the genuine row carrier. -/
def tensorUnitPullbackCoefficientNormalizedOperation :
    originalPrespectrum (boundedFlatPerfectWaldhausen Y) ⟶
      parameterLooping (rowLoopPrespectrum (modelOf (boundedFlatPerfectWaldhausen X))) :=
  rowSelfTrackOperation
    (boundedFlatPerfectTensorUnitPrespectrumMap f ≫
      rowStabilizationMap (modelOf (boundedFlatPerfectWaldhausen X)))
    (tensorUnitPullbackCoefficientRowSpectrumHomotopy f r)

/-- Every positive level uses the original inverse-prefix normalization of the actual cell. -/
theorem tensorUnitPullbackCoefficientNormalizedOperation_succ (k : ℕ)
    (x : stageSpace k (modelOf (boundedFlatPerfectWaldhausen Y))) :
    (tensorUnitPullbackCoefficientNormalizedOperation f r).map (k + 1) x =
      loopNormalizedSelfTrack
        ((boundedFlatPerfectTensorUnitPrespectrumMap f ≫
          rowStabilizationMap (modelOf (boundedFlatPerfectWaldhausen X))).map (k + 1) x)
        (tensorUnitPullbackCoefficientStagePath f r k x) :=
  rowSelfTrackStage_apply _ _ k x

/-- Degree zero retains the unit time, the original input loop, and the coefficient row. -/
theorem tensorUnitPullbackCoefficientNormalizedOperation_zero
    (γ : Path (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen Y)))
      (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen Y)))) (t a s : unitInterval) :
    Path.toContinuousMap (Path.toContinuousMap
      (Path.toContinuousMap
        ((tensorUnitPullbackCoefficientNormalizedOperation f r).map 0 γ) t) a) s =
      loopNormalizedSelfTrack
        ((boundedFlatPerfectTensorUnitPrespectrumMap f ≫
          rowStabilizationMap (modelOf (boundedFlatPerfectWaldhausen X))).map 1 (γ a))
        (tensorUnitPullbackCoefficientStagePath f r 0 (γ a)) t s :=
  congrArg (fun p => p t s)
    (rowSelfTrackStage_apply
      (boundedFlatPerfectTensorUnitPrespectrumMap f ≫
        rowStabilizationMap (modelOf (boundedFlatPerfectWaldhausen X)))
      (tensorUnitPullbackCoefficientRowSpectrumHomotopy f r) 0 (γ a))

end Quillen.PerfectComplexes
