/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitCoefficientStageRealization
public import Quillen.Topology.Prespectrum.Looping

/-!
# The genuine coefficient cell as a whole stabilized spectrum track

Curry the independently realized finite coefficient cells and assemble them into a coherent
prespectrum homotopy. Degree zero uses the original loop extension, with its original input-loop
time explicit. The positive degrees use the actual first coefficient row and unit edge. Equality
with the tensor track followed by the actual loop-tail stabilization is proved for the whole
homotopy. Ordinary loop-tail stabilization is retained literally; it is not parameter looping.
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

/-- Curry the actual coefficient S-row while retaining the forward unit edge as homotopy time. -/
def tensorUnitPullbackCoefficientStageLoop (k : ℕ) :
    C(unitInterval × stageSpace k (modelOf (boundedFlatPerfectWaldhausen Y)),
      Path (stagePoint (k + 1) (modelOf (boundedFlatPerfectWaldhausen X)))
        (stagePoint (k + 1) (modelOf (boundedFlatPerfectWaldhausen X)))) where
  toFun z := {
    toFun s := tensorUnitPullbackCoefficientStageRealization f r k (s, z)
    continuous_toFun := by fun_prop
    source' := by
      rw [tensorUnitPullbackCoefficientStageRealization_structure]
      exact Path.source _
    target' := by
      rw [tensorUnitPullbackCoefficientStageRealization_structure]
      exact Path.target _ }
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    exact (tensorUnitPullbackCoefficientStageRealization f r k).continuous.comp continuous_swap

/-- Every positive-level continuous map is the unchanged structure image of the tensor track. -/
theorem tensorUnitPullbackCoefficientStageLoop_eq (k : ℕ) :
    tensorUnitPullbackCoefficientStageLoop f r k =
      ((boundedFlatPerfectTensorUnitHomotopy f r).postcomp
        (stabilizationMap (originalPrespectrum (boundedFlatPerfectWaldhausen X)))).level (k + 1)
        := by
  apply ContinuousMap.ext
  intro z
  apply Path.ext
  funext s
  exact tensorUnitPullbackCoefficientStageRealization_structure f r k s z.1 z.2

/-- Actual coefficient cells in positive degree, with the original loop extension in degree zero.
-/
def tensorUnitPullbackCoefficientCellLevel (n : ℕ) :
    C(unitInterval × (originalPrespectrum (boundedFlatPerfectWaldhausen Y)).space n,
      (looping (tail (originalPrespectrum (boundedFlatPerfectWaldhausen X)))).space n) :=
  Nat.casesOn n ((boundedFlatPerfectTensorUnitHomotopy f r).level 0)
    (tensorUnitPullbackCoefficientStageLoop f r)

/-- The degree-zero extension retains the input-loop time separately from the unit-edge time. -/
theorem tensorUnitPullbackCoefficientCellLevel_zero (t s : unitInterval)
    (x : Path (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen Y)))
      (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen Y)))) :
    Path.toContinuousMap (tensorUnitPullbackCoefficientCellLevel f r 0 (t, x)) s =
      (boundedFlatPerfectTensorUnitHomotopy f r).level 1 (t, x s) := rfl

/-- Equality of complete continuous levels, without taking homotopy or stable classes. -/
theorem tensorUnitPullbackCoefficientCellLevel_eq (n : ℕ) :
    tensorUnitPullbackCoefficientCellLevel f r n =
      ((boundedFlatPerfectTensorUnitHomotopy f r).postcomp
        (stabilizationMap (originalPrespectrum (boundedFlatPerfectWaldhausen X)))).level n := by
  cases n with
  | zero => rfl
  | succ k => exact tensorUnitPullbackCoefficientStageLoop_eq f r k

/-- The independently realized coefficient cells form a whole structure-compatible homotopy. -/
def tensorUnitPullbackCoefficientSpectrumHomotopy :
    Homotopy
      (boundedFlatPerfectTensorUnitPrespectrumMap f ≫
        stabilizationMap (originalPrespectrum (boundedFlatPerfectWaldhausen X)))
      (boundedFlatPerfectTensorUnitPrespectrumMap f ≫
        stabilizationMap (originalPrespectrum (boundedFlatPerfectWaldhausen X))) where
  level := tensorUnitPullbackCoefficientCellLevel f r
  at_zero n x := by
    rw [tensorUnitPullbackCoefficientCellLevel_eq]
    exact ((boundedFlatPerfectTensorUnitHomotopy f r).postcomp
      (stabilizationMap (originalPrespectrum (boundedFlatPerfectWaldhausen X)))).at_zero n x
  at_one n x := by
    rw [tensorUnitPullbackCoefficientCellLevel_eq]
    exact ((boundedFlatPerfectTensorUnitHomotopy f r).postcomp
      (stabilizationMap (originalPrespectrum (boundedFlatPerfectWaldhausen X)))).at_one n x
  at_point n t := by
    rw [tensorUnitPullbackCoefficientCellLevel_eq]
    exact ((boundedFlatPerfectTensorUnitHomotopy f r).postcomp
      (stabilizationMap (originalPrespectrum (boundedFlatPerfectWaldhausen X)))).at_point n t
  comm n t x s := by
    rw [tensorUnitPullbackCoefficientCellLevel_eq, tensorUnitPullbackCoefficientCellLevel_eq]
    exact ((boundedFlatPerfectTensorUnitHomotopy f r).postcomp
      (stabilizationMap (originalPrespectrum (boundedFlatPerfectWaldhausen X)))).comm n t x s

/-- The complete realized coefficient-cell homotopy is the actual stabilized tensor homotopy. -/
theorem tensorUnitPullbackCoefficientSpectrumHomotopy_eq :
    tensorUnitPullbackCoefficientSpectrumHomotopy f r =
      (boundedFlatPerfectTensorUnitHomotopy f r).postcomp
        (stabilizationMap (originalPrespectrum (boundedFlatPerfectWaldhausen X))) := by
  apply Quillen.LoopPrespectrum.Homotopy.ext
  funext n
  exact tensorUnitPullbackCoefficientCellLevel_eq f r n

end Quillen.PerfectComplexes
