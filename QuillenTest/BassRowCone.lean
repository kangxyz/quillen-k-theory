/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRowRefinement

/-! Regressions for the original Bass-cone row transpose and its degree-zero comparison. -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.LoopPrespectrum
open scoped Topology unitInterval
universe u
namespace QuillenTest.BassRowCone
open Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R)

/-- The proved continuous involution gives an actual homeomorphism of the original cone level. -/
def coneHomeomorph (k : ℕ) :
    (CoefficientBassRowRefinement.source P a).space (k + 3) ≃ₜ
      (CoefficientBassRowRefinement.source P a).space (k + 3) where
  toFun := CoefficientBassRowCone.rowSwap P a k
  invFun := CoefficientBassRowCone.rowSwap P a k
  left_inv := CoefficientBassRowCone.rowSwap_involutive P a k
  right_inv := CoefficientBassRowCone.rowSwap_involutive P a k
  continuous_toFun := (CoefficientBassRowCone.rowSwap P a k).continuous
  continuous_invFun := (CoefficientBassRowCone.rowSwap P a k).continuous

/-- The inverse homeomorphism acts on the entire original cylinder with its height unchanged. -/
theorem coneHomeomorph_inverse_cylinder (k : ℕ) (h : unitInterval)
    (x : (Quillen.Waldhausen.IteratedS.RowHomotopyPushout.spectrum
      (CoefficientBassRowCone.projection P a) (CoefficientBassRowCone.projection P a)).space
        (k + 3)) :
    (coneHomeomorph P a k).symm
      ((mappingConeHomotopy (boundedFlatCoefficientBassSquareComparison P a)).level (k + 3)
        (h, x)) =
      (mappingConeHomotopy (boundedFlatCoefficientBassSquareComparison P a)).level (k + 3)
        (h, CoefficientBassRowCone.spanRowSwap P a k x) := rfl

/-- The actual degree-zero comm square retains both original structure times. -/
theorem zero_structure (x : (CoefficientBassRowRefinement.source P a).space 0)
    (r s : unitInterval) :
    Path.toContinuousMap
      (Path.toContinuousMap
        ((CoefficientBassRowRefinement.carrier P a).structureMap 0
          ((CoefficientBassRowRefinement.comparison P a).map 0 x)) r) s =
      (CoefficientBassRowRefinement.source P a).structureMap 1
        ((CoefficientBassRowRefinement.source P a).structureMap 0 x r) s := rfl

end QuillenTest.BassRowCone
