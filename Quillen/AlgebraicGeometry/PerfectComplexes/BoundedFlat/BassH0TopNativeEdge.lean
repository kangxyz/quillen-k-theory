/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassH0CommonReference

/-! The fourth H0 edge has exactly the required original native M endpoint value.
This does not supply a two-parameter scalar family for M. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Opposite Convexity
open Quillen.PolynomialBaseChange Quillen.Scheme.CoefficientBaseChange
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters Quillen.LoopPrespectrum
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassH0Merge
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- The whole original top edge of H0 agrees with the fixed native M face at r = 0. -/
theorem top_native_edge (n : ℕ) (t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P u v) n (BassH0Diagram.parameter (1, t), x) =
      ((boundedFlatCoefficientPolynomialSpanCompositionHomotopy P u v).postcomp
        (boundedFlatCoefficientBassSquareComparison P c)).level n
          (0, HomotopyPushout.cylinder
            (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
            (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)) n (t, x)) := by
  rw [simplex_original, BassH0Diagram.composition_H0]
  exact ((boundedFlatCoefficientBassComparisonHomotopy P (u ≫ v)).at_one n _).trans
    (((boundedFlatCoefficientPolynomialSpanCompositionHomotopy P u v).postcomp
      (boundedFlatCoefficientBassSquareComparison P c)).at_zero n _).symm

end Quillen.PerfectComplexes.BassH0Merge
