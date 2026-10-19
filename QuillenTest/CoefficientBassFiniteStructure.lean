/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassFiniteStructure

/-! Regression for the eventual range and the literal positive comparison map. -/
noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen Quillen.LoopPrespectrum Quillen.PerfectComplexes
universe u

example {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R)
    (n k : ℕ) (hn : 2 ≤ n) (hk : k + 2 < 2 * n - 2) :
    Function.Bijective (homotopyGroupMap (N := Fin (k + 2))
      ((CoefficientBassRowRefinement.source P a).structureMap (n + 1))
      ((CoefficientBassRowRefinement.source P a).map_point (n + 1))) := by
  rw [show n + 1 = (n - 2) + 3 by omega]
  exact CoefficientBassRowRefinement.source_structure_bijective P a (n - 2) k (by omega)

example {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R) (n : ℕ) :
    (CoefficientBassRowRefinement.comparison P a).map (n + 1) =
      (CoefficientBassRowRefinement.source P a).structureMap (n + 1) :=
  CoefficientBassRowRefinement.comparison_succ P a n
