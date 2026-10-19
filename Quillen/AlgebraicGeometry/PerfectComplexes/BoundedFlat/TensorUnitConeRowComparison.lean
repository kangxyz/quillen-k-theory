/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRowCone

/-!
# Row interchange on the actual tensor-unit cone track and its prescribed null

The genuine tensor unitor and forward Laurent-unit tracks descend through the unchanged Bass
cofiber inclusion. Their entire row squares retain the original unit time. Concatenating the
unitor movement with the original positive source null preserves its prescribed two-half clock,
so the tensor/null word has the actual row compatibility needed by a row-loop refinement.
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

/-- The full genuine tensor track retains its row square after the same cofiber inclusion. -/
theorem boundedFlatCoefficientTensorConeTrack_rowSwap (k : ℕ) (t : unitInterval)
    (x : stageSpace (k + 2) (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))) :
    CoefficientBassRowCone.rowSwap P a k
      ((boundedFlatCoefficientTensorConeTrack P a).level (k + 3) (t, x)) =
    (boundedFlatCoefficientTensorConeTrack P a).level (k + 3)
      (t, stageRowSwapHomeomorph k (modelOf (boundedFlatPerfectWaldhausen (space (op P, a)))) x)
      := by
  change CoefficientBassRowCone.rowSwap P a k
    ((mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a)).map (k + 3)
      ((boundedFlatCoefficientTensorUnitHomotopy P a).level (k + 3) (t, x))) = _
  rw [CoefficientBassRowCone.rowSwap_inclusion]
  exact congrArg ((mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a)).map
    (k + 3)) (boundedFlatPerfectTensorUnitHomotopy_rowSwap (laurentProjection P a)
      (boundedFlatCoefficientUnit (op P, (laurentUnderFunctor R).obj a)
        (AlgebraicGeometry.Scheme.PolynomialLaurent.laurentGlobalUnit a.right)) k t x)

/-- The genuine tensor unitor movement retains every original time after cone inclusion. -/
theorem boundedFlatCoefficientTensorConeMovement_rowSwap (k : ℕ) (t : unitInterval)
    (x : stageSpace (k + 2) (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))) :
    CoefficientBassRowCone.rowSwap P a k
      ((boundedFlatCoefficientTensorConeMovement P a).level (k + 3) (t, x)) =
    (boundedFlatCoefficientTensorConeMovement P a).level (k + 3)
      (t, stageRowSwapHomeomorph k (modelOf (boundedFlatPerfectWaldhausen (space (op P, a)))) x)
      := by
  change CoefficientBassRowCone.rowSwap P a k
    ((mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a)).map (k + 3)
      ((boundedFlatPerfectTensorUnitUnitorHomotopy (laurentProjection P a)).level
        (k + 3) (t, x))) = _
  rw [CoefficientBassRowCone.rowSwap_inclusion]
  exact congrArg ((mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a)).map
    (k + 3)) (boundedFlatPerfectTensorUnitUnitorHomotopy_rowSwap
      (laurentProjection P a) k t x)

/-- The actual tensor null preserves both original halves of its specified concatenation. -/
theorem boundedFlatCoefficientTensorConeNull_rowSwap (k : ℕ) (t : unitInterval)
    (x : stageSpace (k + 2) (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))) :
    CoefficientBassRowCone.rowSwap P a k
      ((boundedFlatCoefficientTensorConeNull P a).level (k + 3) (t, x)) =
    (boundedFlatCoefficientTensorConeNull P a).level (k + 3)
      (t, stageRowSwapHomeomorph k (modelOf (boundedFlatPerfectWaldhausen (space (op P, a)))) x)
      := by
  let H := boundedFlatCoefficientTensorConeMovement P a
  let K := boundedFlatCoefficientBassLaurentNullHomotopy P a
  change CoefficientBassRowCone.rowSwap P a k
    (((H.levelHomotopy (k + 3)).trans (K.levelHomotopy (k + 3))) (t, x)) =
      ((H.levelHomotopy (k + 3)).trans (K.levelHomotopy (k + 3)))
        (t, stageRowSwapHomeomorph k
          (modelOf (boundedFlatPerfectWaldhausen (space (op P, a)))) x)
  rw [ContinuousMap.HomotopyRel.trans_apply, ContinuousMap.HomotopyRel.trans_apply]
  split
  · exact boundedFlatCoefficientTensorConeMovement_rowSwap P a k _ x
  · exact CoefficientBassRowCone.sourceNull_rowSwap P a k _ x

end Quillen.PerfectComplexes
