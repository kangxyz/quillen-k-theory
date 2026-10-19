/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalTensorInitialCell

/-! Whole initial-cell endpoint regression with the actual stabilization retained. -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.PerfectComplexes Quillen.PerfectComplexes.GlobalSectionChangeIndex
open Quillen.Waldhausen.IteratedS Quillen.KTheory.Bass Quillen.LoopPrespectrum
open CommRingCat.PolynomialLaurent
universe u
namespace QuillenTest.GlobalTensorInitialCell

/-- The final face is the independently realized whole cell, at every spectrum level. -/
theorem original_cell_face {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R)
    (n : ℕ) (x : (prespectrum ((globalRow P).obj a)).space n) :
    (initialCellSeedComparison P a).level n (1, x) =
      (boundedFlatCoefficientCellBassTransition P a).map n
        ((boundedFlatCoefficientSectionEvaluationPrespectrumMap (op P, a)).map n
          ((prespectrumMap ((rowRestriction P).app a)).map n x)) :=
  (initialCellSeedComparison P a).at_one n x

end QuillenTest.GlobalTensorInitialCell
