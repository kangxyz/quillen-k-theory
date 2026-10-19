/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import
Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitCoefficientRowStableRepresentative

/-!
The independently normalized coefficient roof computes the original scalar Bass action under
all integer-graded stable homotopy functors. This consumer uses the whole localized equality,
so it never attempts to detect a spectrum morphism from its group maps. It also checks that
any homotopy-invariant stable target functor preserves the explicit roof computation.
-/
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.PerfectComplexes Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u v w

/-- The fixed normalized operation computes the same original map in every signed stable degree.
-/
example {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R) (d : ℤ) :
    (localizedStableHomotopyFunctor d).map
        (boundedFlatCoefficientNormalizedCellLocalizedArrow P a) =
      (stableHomotopyFunctor d).map (boundedFlatCoefficientBassTransition P a) := by
  rw [boundedFlatCoefficientNormalizedCellLocalizedArrow_seed]
  rfl

/-- Every actual target functor on the localization preserves this specific whole roof identity.
-/
example {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R)
    {D : Type v} [Category.{w} D] (T : StableLocalization.{u + 1} ⥤ D) :
    T.map (boundedFlatCoefficientNormalizedCellLocalizedArrow P a) =
      (toStableLocalization ⋙ T).map (boundedFlatCoefficientBassTransition P a) := by
  rw [boundedFlatCoefficientNormalizedCellLocalizedArrow_seed]
  rfl
