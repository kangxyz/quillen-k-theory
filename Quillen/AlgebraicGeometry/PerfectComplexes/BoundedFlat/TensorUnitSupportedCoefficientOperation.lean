/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitSupportedCoefficientSpectrum
public import Quillen.Waldhausen.SConstruction.Iterated.RowSelfTrackOperation

/-!
# Original inverse-prefix normalization of the supported first tensor coefficient cell

The input is the independently constructed supported row cell. The target is its genuine
row-loop spectrum, with the zero-level transpose and all original interval coordinates retained.
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
variable {S T : Scheme.OpenPairs.{u}} (p : S ⟶ T) (r : (Γ(S.obj.right, ⊤))ˣ)

/-- The standard inverse-prefix operation on the genuine supported first-row cell. -/
def tensorSupportedPairCoefficientOperation :=
  rowSelfTrackOperation
    (tensorSupportedPairPrespectrumMap p ≫
      rowStabilizationMap (modelOf (boundedFlatPerfectSupportedWaldhausen S.obj.hom)))
    (tensorSupportedPairCoefficientSpectrumHomotopy p r)

/-- Every positive level keeps the original normalization word of the actual supported cell. -/
theorem tensorSupportedPairCoefficientOperation_succ (k : ℕ)
    (x : stageSpace k (modelOf (boundedFlatPerfectSupportedWaldhausen T.obj.hom))) :
    (tensorSupportedPairCoefficientOperation p r).map (k + 1) x =
      loopNormalizedSelfTrack
        ((tensorSupportedPairPrespectrumMap p ≫
          rowStabilizationMap (modelOf (boundedFlatPerfectSupportedWaldhausen S.obj.hom))).map
          (k + 1) x)
        (((tensorSupportedPairCoefficientSpectrumHomotopy p r).levelHomotopy
          (k + 1)).toHomotopy.evalAt x) :=
  rowSelfTrackStage_apply _ _ k x

/-- The original zero extension retains unit, input-loop and row times separately. -/
theorem tensorSupportedPairCoefficientOperation_zero
    (γ : Path (stagePoint 0 (modelOf (boundedFlatPerfectSupportedWaldhausen T.obj.hom)))
      (stagePoint 0 (modelOf (boundedFlatPerfectSupportedWaldhausen T.obj.hom))))
    (t a s : unitInterval) :
    Path.toContinuousMap (Path.toContinuousMap (Path.toContinuousMap
      ((tensorSupportedPairCoefficientOperation p r).map 0 γ) t) a) s =
      Path.toContinuousMap (Path.toContinuousMap
        (rowSelfTrackStage
          (tensorSupportedPairPrespectrumMap p ≫
            rowStabilizationMap (modelOf (boundedFlatPerfectSupportedWaldhausen S.obj.hom)))
          (tensorSupportedPairCoefficientSpectrumHomotopy p r) 0 (γ a)) t) s :=
  rowSelfTrackOperation_zero _ _ γ t a s

end Quillen.PerfectComplexes
