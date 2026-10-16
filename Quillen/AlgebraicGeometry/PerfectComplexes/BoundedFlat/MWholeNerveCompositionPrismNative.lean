/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeNerveCompositionPrisms

/-! # Whole original native families and side surfaces of the composition prisms

The accepted compact evaluator recovers the literal finite product at every level. Each
of the four varying H0 edge paths is retained by name and with its original reversals and
parentheses. The independent composition, H0 and native structure times remain unchanged.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters Quillen.NativePathCells
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassMWholeNerve
open BassReferenceMerge BassH0Merge BassH1Join
attribute [local irreducible] boundedFlatNormalizedPullback

open ProjectionRectangleParameters
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c d : Under R} (u : a ⟶ b) (v : b ⟶ c) (w : c ⟶ d)

/-- Compact evaluation recovers the entire original laurent finite-product family. -/
theorem laurent_prism_compact_native (n : ℕ) (q s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    CommonReferenceNerve.compactPrespectrumFamily _ (laurentPrism P u v w) n
      (![q, s, t], x) =
      (boundedFlatCoefficientLaurentCompositionHomotopy P v w).level n
        (q, prespectrumSimplexFamily (BassH0Diagram.simplex P u) n
          (BassH0Diagram.parameter (s, t), x)) := by
  exact (CommonReferenceNerve.compactPrespectrumFamily_eq_simplex _ (laurentPrism P u v w)
    (laurentPrismNodes P u v w) ![q, s, t] (laurentPrismParameter.{u} ![q, s, t]) rfl n x).trans
      (laurent_prism_native P u v w n q s t x)

/-- The entire varying bottom side retains its exact original named H0 path. -/
theorem laurent_prism_bottom_side (n : ℕ) (q t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    CommonReferenceNerve.compactPrespectrumFamily _ (laurentPrism P u v w) n
      (![q, 0, t], x) =
      (boundedFlatCoefficientLaurentCompositionHomotopy P v w).level n
        (q, prespectrumSimplexFamily (BassH0Diagram.simplex P u) n
          (((D BassH0Diagram.plusFace).symm.trans (D BassH0Diagram.minusFace)) t, x)) := by
  rw [laurent_prism_compact_native, BassH0Diagram.parameter_zero]

/-- The entire varying top side retains its exact original named H0 path. -/
theorem laurent_prism_top_side (n : ℕ) (q t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    CommonReferenceNerve.compactPrespectrumFamily _ (laurentPrism P u v w) n
      (![q, 1, t], x) =
      (boundedFlatCoefficientLaurentCompositionHomotopy P v w).level n
        (q, prespectrumSimplexFamily (BassH0Diagram.simplex P u) n
          (((Ppath BassH0Diagram.plusFace).trans
            (((K BassH0Diagram.plusFace).symm.trans (K BassH0Diagram.minusFace)).trans
              (Ppath BassH0Diagram.minusFace).symm)) t, x)) := by
  rw [laurent_prism_compact_native, BassH0Diagram.parameter_one]

/-- The entire varying plus side retains its exact original named H0 path. -/
theorem laurent_prism_plus_side (n : ℕ) (q s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    CommonReferenceNerve.compactPrespectrumFamily _ (laurentPrism P u v w) n
      (![q, s, 0], x) =
      (boundedFlatCoefficientLaurentCompositionHomotopy P v w).level n
        (q, prespectrumSimplexFamily (BassH0Diagram.simplex P u) n
          (L BassH0Diagram.plusFace s, x)) := by
  rw [laurent_prism_compact_native, BassH0Diagram.parameter_left]

/-- The entire varying minus side retains its exact original named H0 path. -/
theorem laurent_prism_minus_side (n : ℕ) (q s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    CommonReferenceNerve.compactPrespectrumFamily _ (laurentPrism P u v w) n
      (![q, s, 1], x) =
      (boundedFlatCoefficientLaurentCompositionHomotopy P v w).level n
        (q, prespectrumSimplexFamily (BassH0Diagram.simplex P u) n
          (L BassH0Diagram.minusFace s, x)) := by
  rw [laurent_prism_compact_native, BassH0Diagram.parameter_right]

/-- Compact evaluation recovers the entire original coefficient finite-product family. -/
theorem coefficient_prism_compact_native (n : ℕ) (q s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    CommonReferenceNerve.compactPrespectrumFamily _ (coefficientPrism P u v w) n
      (![q, s, t], x) =
      prespectrumSimplexFamily (BassH0Diagram.simplex P w) n
        (BassH0Diagram.parameter (s, t),
          (boundedFlatCoefficientCompositionHomotopy P u v).level n (q, x)) := by
  exact (CommonReferenceNerve.compactPrespectrumFamily_eq_simplex _ (coefficientPrism P u v w)
    (coefficientPrismNodes P u v w) ![q, s, t]
      (coefficientPrismParameter.{u} ![q, s, t]) rfl n x).trans
      (coefficient_prism_native P u v w n q s t x)

/-- The entire varying bottom side retains its exact original named H0 path. -/
theorem coefficient_prism_bottom_side (n : ℕ) (q t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    CommonReferenceNerve.compactPrespectrumFamily _ (coefficientPrism P u v w) n
      (![q, 0, t], x) =
      prespectrumSimplexFamily (BassH0Diagram.simplex P w) n
        (((D BassH0Diagram.plusFace).symm.trans (D BassH0Diagram.minusFace)) t,
          (boundedFlatCoefficientCompositionHomotopy P u v).level n (q, x)) := by
  rw [coefficient_prism_compact_native, BassH0Diagram.parameter_zero]

/-- The entire varying top side retains its exact original named H0 path. -/
theorem coefficient_prism_top_side (n : ℕ) (q t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    CommonReferenceNerve.compactPrespectrumFamily _ (coefficientPrism P u v w) n
      (![q, 1, t], x) =
      prespectrumSimplexFamily (BassH0Diagram.simplex P w) n
        (((Ppath BassH0Diagram.plusFace).trans
            (((K BassH0Diagram.plusFace).symm.trans (K BassH0Diagram.minusFace)).trans
              (Ppath BassH0Diagram.minusFace).symm)) t,
          (boundedFlatCoefficientCompositionHomotopy P u v).level n (q, x)) := by
  rw [coefficient_prism_compact_native, BassH0Diagram.parameter_one]

/-- The entire varying plus side retains its exact original named H0 path. -/
theorem coefficient_prism_plus_side (n : ℕ) (q s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    CommonReferenceNerve.compactPrespectrumFamily _ (coefficientPrism P u v w) n
      (![q, s, 0], x) =
      prespectrumSimplexFamily (BassH0Diagram.simplex P w) n
        (L BassH0Diagram.plusFace s,
          (boundedFlatCoefficientCompositionHomotopy P u v).level n (q, x)) := by
  rw [coefficient_prism_compact_native, BassH0Diagram.parameter_left]

/-- The entire varying minus side retains its exact original named H0 path. -/
theorem coefficient_prism_minus_side (n : ℕ) (q s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    CommonReferenceNerve.compactPrespectrumFamily _ (coefficientPrism P u v w) n
      (![q, s, 1], x) =
      prespectrumSimplexFamily (BassH0Diagram.simplex P w) n
        (L BassH0Diagram.minusFace s,
          (boundedFlatCoefficientCompositionHomotopy P u v).level n (q, x)) := by
  rw [coefficient_prism_compact_native, BassH0Diagram.parameter_right]

end Quillen.PerfectComplexes.BassMWholeNerve
