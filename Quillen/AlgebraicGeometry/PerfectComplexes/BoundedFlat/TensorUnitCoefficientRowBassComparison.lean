/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitCoefficientNormalizedOperation
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitRowBassNormalization
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRowInclusion

/-!
# The independently normalized first-coefficient cell after the original Bass cofiber

The actual normalized first-S tensor cell is sent through the original cofiber row map. Its
whole map equals the normalized original tensor track in the actual row-refined cone. The
proved parameterized normalization then gives a whole spectrum homotopy to the original
null-conjugated tensor seed followed by the same comparison. All original parameter orders,
zero levels, and cone maps remain explicit. The iterated-S level is not a Bass-stage index.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open CommRingCat.PolynomialLaurent
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R)

/-- The independently normalized first coefficient cell after the actual cofiber row inclusion.
-/
def boundedFlatCoefficientNormalizedCellBass :
    originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a))) ⟶
      parameterLooping (CoefficientBassRowRefinement.carrier P a) :=
  tensorUnitPullbackCoefficientNormalizedOperation (laurentProjection P a)
    (boundedFlatCoefficientUnit (op P, (laurentUnderFunctor R).obj a)
      (AlgebraicGeometry.Scheme.PolynomialLaurent.laurentGlobalUnit a.right)) ≫
    parameterLoopingMap (CoefficientBassRowRefinement.inclusionRow P a)

/-- The full normalized positive cell preserves the original cofiber map and both cell times. -/
theorem boundedFlatCoefficientNormalizedCellBass_stage (k : ℕ)
    (x : stageSpace k (modelOf (boundedFlatPerfectWaldhausen (space (op P, a)))))
    (t s : unitInterval) :
    (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a)).map (k + 2)
      (Path.toContinuousMap (Path.toContinuousMap
        ((tensorUnitPullbackCoefficientNormalizedOperation (laurentProjection P a)
          (boundedFlatCoefficientUnit (op P, (laurentUnderFunctor R).obj a)
            (AlgebraicGeometry.Scheme.PolynomialLaurent.laurentGlobalUnit a.right))).map
              (k + 1) x) t) s) =
    RowRefinement.normalizedStage (CoefficientBassRowCone.rowSwap P a)
      (CoefficientBassRowCone.rowSwap_point P a) (boundedFlatCoefficientTensorRowEndpoint P a)
      (boundedFlatCoefficientTensorRowTrack P a) k x t s := by
  rw [tensorUnitPullbackCoefficientNormalizedOperation_succ, RowRefinement.normalizedStage_apply]
  apply loopNormalizedSelfTrack_pointwise
    ((mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a)).map (k + 2)) id
  · intro b
    exact congrArg (fun p => p b)
      ((mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a)).comm (k + 1)
        ((boundedFlatPerfectTensorUnitPrespectrumMap (laurentProjection P a)).map (k + 1) x))
  · intro b c
    change (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a)).map (k + 2)
      (tensorUnitPullbackCoefficientStageRealization (laurentProjection P a)
        (boundedFlatCoefficientUnit (op P, (laurentUnderFunctor R).obj a)
          (AlgebraicGeometry.Scheme.PolynomialLaurent.laurentGlobalUnit a.right))
        k (c, (b, x))) = _
    rw [tensorUnitPullbackCoefficientStageRealization_structure]
    exact congrArg (fun p => p c)
      ((mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a)).comm (k + 1)
        ((boundedFlatCoefficientTensorUnitHomotopy P a).level (k + 1) (b, x)))

/-- The independent normalized first-S cell and the normalized tensor-cone track agree as maps.
-/
theorem boundedFlatCoefficientNormalizedCellBass_eq :
    boundedFlatCoefficientNormalizedCellBass P a =
      boundedFlatCoefficientTensorRowNormalizedBass P a := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  cases n with
  | zero =>
    apply Path.ext
    funext t
    apply Path.ext
    funext r
    apply Path.ext
    funext s
    exact boundedFlatCoefficientNormalizedCellBass_stage P a 0
      ((originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).structureMap 0 x r)
      t s
  | succ k =>
    apply Path.ext
    funext t
    apply Path.ext
    funext s
    exact boundedFlatCoefficientNormalizedCellBass_stage P a k x t s

/-- The actual first-S operation has a whole spectrum comparison to the same original Bass seed.
-/
def boundedFlatCoefficientNormalizedCellBassHomotopy :
    Homotopy (boundedFlatCoefficientNormalizedCellBass P a)
      (boundedFlatCoefficientTensorBassTransition P a ≫
        parameterLoopingMap (CoefficientBassRowRefinement.comparison P a)) :=
  (boundedFlatCoefficientTensorRowNormalization P a).cast
    (boundedFlatCoefficientNormalizedCellBass_eq P a).symm rfl

/-- The genuine normalized cell compares to the original forward scalar Bass seed as a whole track.
-/
def boundedFlatCoefficientNormalizedCellScalarHomotopy :
    Homotopy (boundedFlatCoefficientNormalizedCellBass P a)
      (boundedFlatCoefficientBassTransition P a ≫
        parameterLoopingMap (CoefficientBassRowRefinement.comparison P a)) :=
  (boundedFlatCoefficientNormalizedCellBassHomotopy P a).trans
    ((boundedFlatCoefficientTensorBassTransitionHomotopy P a).postcomp
      (parameterLoopingMap (CoefficientBassRowRefinement.comparison P a)))

end Quillen.PerfectComplexes
