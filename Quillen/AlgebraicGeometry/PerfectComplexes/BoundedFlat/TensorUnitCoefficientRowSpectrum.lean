/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitCoefficientSpectrum
public import Quillen.Waldhausen.SConstruction.Iterated.RowLoopPrespectrum

/-!
# The genuine tensor coefficient cell in the distinguished-row prespectrum

The independently realized first coefficient row supplies every positive level. Degree zero is
its actual loop extension, retaining the input-loop time separately from the coefficient row
and the forward unit edge. These cells assemble into a whole prespectrum homotopy through the
genuine row-stabilization map. This target has the proved row-transposed structure, rather than
the ordinary looped-tail structure. Standard inverse-prefix normalization remains separate.
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

/-- The actual positive coefficient cell is fixed on the original zero input. -/
theorem tensorUnitPullbackCoefficientStageLoop_point (k : ℕ) (t : unitInterval) :
    tensorUnitPullbackCoefficientStageLoop f r k
      (t, stagePoint k (modelOf (boundedFlatPerfectWaldhausen Y))) =
        Path.refl (stagePoint (k + 1) (modelOf (boundedFlatPerfectWaldhausen X))) := by
  rw [tensorUnitPullbackCoefficientStageLoop_eq]
  exact ((boundedFlatPerfectTensorUnitHomotopy f r).postcomp
    (stabilizationMap (originalPrespectrum (boundedFlatPerfectWaldhausen X)))).at_point (k + 1) t

/-- The actual first-row cell extended over the original degree-zero input loop. -/
def tensorUnitPullbackCoefficientRowZero :
    C(unitInterval × Path (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen Y)))
      (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen Y))),
      Path (Path.refl (stagePoint 1 (modelOf (boundedFlatPerfectWaldhausen X))))
        (Path.refl (stagePoint 1 (modelOf (boundedFlatPerfectWaldhausen X))))) where
  toFun z := {
    toFun a := tensorUnitPullbackCoefficientStageLoop f r 0 (z.1, z.2 a)
    continuous_toFun := by fun_prop
    source' := by
      rw [Path.source]
      exact tensorUnitPullbackCoefficientStageLoop_point f r 0 z.1
    target' := by
      rw [Path.target]
      exact tensorUnitPullbackCoefficientStageLoop_point f r 0 z.1 }
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    change Continuous (fun z : (unitInterval ×
      Path (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen Y)))
        (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen Y)))) × unitInterval =>
          tensorUnitPullbackCoefficientStageLoop f r 0 (z.1.1, z.1.2 z.2))
    fun_prop

/-- Every independent input-loop, coefficient-row, and unit-edge time is displayed. -/
theorem tensorUnitPullbackCoefficientRowZero_apply (t a s : unitInterval)
    (γ : Path (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen Y)))
      (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen Y)))) :
    tensorUnitPullbackCoefficientRowZero f r (t, γ) a s =
      tensorUnitPullbackCoefficientStageRealization f r 0 (s, (t, γ a)) := rfl

/-- The original independently realized cells, with the genuine row-target zero extension. -/
def tensorUnitPullbackCoefficientRowLevel (n : ℕ) :
    C(unitInterval × (originalPrespectrum (boundedFlatPerfectWaldhausen Y)).space n,
      (rowLoopPrespectrum (modelOf (boundedFlatPerfectWaldhausen X))).space n) :=
  Nat.casesOn n (tensorUnitPullbackCoefficientRowZero f r)
    (tensorUnitPullbackCoefficientStageLoop f r)

/-- Equality of complete continuous levels with the actual row-stabilized tensor track. -/
theorem tensorUnitPullbackCoefficientRowLevel_eq (n : ℕ) :
    tensorUnitPullbackCoefficientRowLevel f r n =
      ((boundedFlatPerfectTensorUnitHomotopy f r).postcomp
        (rowStabilizationMap (modelOf (boundedFlatPerfectWaldhausen X)))).level n := by
  cases n with
  | zero =>
    apply ContinuousMap.ext
    intro z
    change unitInterval × Path (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen Y)))
      (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen Y))) at z
    apply Path.ext
    funext a
    apply Path.ext
    funext s
    exact tensorUnitPullbackCoefficientStageRealization_structure f r 0 s z.1 (z.2 a)
  | succ k => exact tensorUnitPullbackCoefficientStageLoop_eq f r k

/-- The genuine first-row cells form a complete homotopy in the row-compatible spectrum target. -/
def tensorUnitPullbackCoefficientRowSpectrumHomotopy :
    Homotopy
      (boundedFlatPerfectTensorUnitPrespectrumMap f ≫
        rowStabilizationMap (modelOf (boundedFlatPerfectWaldhausen X)))
      (boundedFlatPerfectTensorUnitPrespectrumMap f ≫
        rowStabilizationMap (modelOf (boundedFlatPerfectWaldhausen X))) where
  level := tensorUnitPullbackCoefficientRowLevel f r
  at_zero n x := by
    rw [tensorUnitPullbackCoefficientRowLevel_eq]
    exact ((boundedFlatPerfectTensorUnitHomotopy f r).postcomp
      (rowStabilizationMap (modelOf (boundedFlatPerfectWaldhausen X)))).at_zero n x
  at_one n x := by
    rw [tensorUnitPullbackCoefficientRowLevel_eq]
    exact ((boundedFlatPerfectTensorUnitHomotopy f r).postcomp
      (rowStabilizationMap (modelOf (boundedFlatPerfectWaldhausen X)))).at_one n x
  at_point n t := by
    rw [tensorUnitPullbackCoefficientRowLevel_eq]
    exact ((boundedFlatPerfectTensorUnitHomotopy f r).postcomp
      (rowStabilizationMap (modelOf (boundedFlatPerfectWaldhausen X)))).at_point n t
  comm n t x s := by
    rw [tensorUnitPullbackCoefficientRowLevel_eq, tensorUnitPullbackCoefficientRowLevel_eq]
    exact ((boundedFlatPerfectTensorUnitHomotopy f r).postcomp
      (rowStabilizationMap (modelOf (boundedFlatPerfectWaldhausen X)))).comm n t x s

/-- The entire coefficient-cell track is the original tensor track followed by the actual row map.
-/
theorem tensorUnitPullbackCoefficientRowSpectrumHomotopy_eq :
    tensorUnitPullbackCoefficientRowSpectrumHomotopy f r =
      (boundedFlatPerfectTensorUnitHomotopy f r).postcomp
        (rowStabilizationMap (modelOf (boundedFlatPerfectWaldhausen X))) := by
  apply Quillen.LoopPrespectrum.Homotopy.ext
  funext n
  exact tensorUnitPullbackCoefficientRowLevel_eq f r n

end Quillen.PerfectComplexes
