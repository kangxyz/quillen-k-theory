/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitCoefficientStableRepresentative
import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitCoefficientKOne

/-!
Regression for the actual coefficient row, forward Laurent representative, and the entire
stabilized Bass cell/null map. These tests keep the original polynomial restriction and both
independent cell times. They do not assert the separate K-one normalization prism.
-/
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.PerfectComplexes Quillen.Waldhausen Quillen.Waldhausen.IteratedS
open Quillen.LoopPrespectrum AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open scoped Topology unitInterval
universe u

/-- The independent first coefficient row retains the original forward polynomial-to-Laurent
K-one representative, through the literal bounded-flat perfect inclusion. -/
example (R : CommRingCat.{u}) :
    KMap (boundedFlatPerfectInclusion_exact (Spec (.of (LaurentPolynomial R)))) 1
        (tensorUnitCoefficientKOneClass (Spec (.of (LaurentPolynomial R)))
          (laurentGlobalUnit R)) =
      perfectOpenKRestrict (laurentPlus R) 1
        (perfectScalarForwardKOneClass (laurentPlus R)
          (rankOnePerfect (Spec (.of (Polynomial R)))) (polynomialGlobalCoordinate R)
          (laurentGlobalUnit R) (polynomialGlobalCoordinate_laurentPlus R)) := by
  rw [tensorUnitCoefficientKOneClass_inclusion,
    polynomialScalarForwardKOneClass_restrict_rankOne]

/-- The entire actual cell/null map retains the original word at every spectrum level and time.
-/
example {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R) (n : ℕ)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n)
    (t s : unitInterval) :
    Path.toContinuousMap
        (Path.toContinuousMap ((boundedFlatCoefficientCellBassTransition P a).map n x) t) s =
      (mappingCone (boundedFlatCoefficientBassSquareComparison P a)).structureMap n
        (((boundedFlatCoefficientTensorConeTrack P a).conjugateToZero
          (boundedFlatCoefficientTensorConeNull P a)).level n (t, x)) s :=
  boundedFlatCoefficientCellBassTransition_word P a n x t s

/-- The specified actual stable denominator, followed by its genuine localization inverse,
recovers the original scalar Bass seed as a whole localization morphism. -/
example {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R) :
    toStableLocalization.map (boundedFlatCoefficientCellBassTransition P a) ≫
      (stableLocalizationIso (boundedFlatCoefficientCellRefinement P a)
        (boundedFlatCoefficientCellRefinement_isStableEquivalence P a)).inv =
      toStableLocalization.map (boundedFlatCoefficientBassTransition P a) :=
  boundedFlatCoefficientCellLocalizedArrow_seed P a
