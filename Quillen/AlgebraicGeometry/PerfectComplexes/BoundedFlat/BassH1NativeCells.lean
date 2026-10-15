/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Aglib.Algebra.Polynomial.Laurent.UnderSquare
public import Quillen.Topology.Prespectrum.NativeH1CellOps
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassH1References

/-! Exact evaluation of every original H1 parameter cell, with the literal native time coordinates.
The scalar component families are not yet identified on their shared cell boundaries. -/
@[expose] public section

open CommRingCat.PolynomialLaurent

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters Quillen.LoopPrespectrum
open Quillen.NativePathCells
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassH1NativeCells
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- Exact first half of the unchanged original pasted Bass comparison. -/
theorem first_half (n : ℕ) (s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    (boundedFlatCoefficientBassCompositeComparison P u v).level n
      (lower s, HomotopyPushout.cylinder
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)) n (t, x)) =
      (boundedFlatPerfectPrespectrumMap
        (coefficientMap P ((laurentUnderFunctor R).map v))).map n
          ((boundedFlatCoefficientBassComparisonHomotopy P u).level n
            (s, HomotopyPushout.cylinder
              (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
              (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)) n (t, x))) :=
  coneSquarePasted_lower_cell
    (boundedFlatCoefficientBassSquareComparison P a)
    (boundedFlatCoefficientBassSquareComparison P b)
    (boundedFlatCoefficientBassSquareComparison P c)
    (boundedFlatCoefficientPolynomialSpanMap P u)
    (boundedFlatPerfectPrespectrumMap (coefficientMap P ((laurentUnderFunctor R).map u)))
    (boundedFlatCoefficientPolynomialSpanMap P v)
    (boundedFlatPerfectPrespectrumMap (coefficientMap P ((laurentUnderFunctor R).map v)))
    (boundedFlatCoefficientBassComparisonHomotopy P u)
    (boundedFlatCoefficientBassComparisonHomotopy P v) n s _

/-- Exact second half, on the actual span-u image of every original cylinder point. -/
theorem second_half (n : ℕ) (s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    (boundedFlatCoefficientBassCompositeComparison P u v).level n
      (upper s, HomotopyPushout.cylinder
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)) n (t, x)) =
      (boundedFlatCoefficientBassComparisonHomotopy P v).level n
        (s, (boundedFlatCoefficientPolynomialSpanMap P u).map n
          (HomotopyPushout.cylinder
            (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
            (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)) n (t, x))) :=
  coneSquarePasted_upper_cell
    (boundedFlatCoefficientBassSquareComparison P a)
    (boundedFlatCoefficientBassSquareComparison P b)
    (boundedFlatCoefficientBassSquareComparison P c)
    (boundedFlatCoefficientPolynomialSpanMap P u)
    (boundedFlatPerfectPrespectrumMap (coefficientMap P ((laurentUnderFunctor R).map u)))
    (boundedFlatCoefficientPolynomialSpanMap P v)
    (boundedFlatPerfectPrespectrumMap (coefficientMap P ((laurentUnderFunctor R).map v)))
    (boundedFlatCoefficientBassComparisonHomotopy P u)
    (boundedFlatCoefficientBassComparisonHomotopy P v) n s _

theorem span_lower (n : ℕ) (t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    (boundedFlatCoefficientPolynomialSpanMap P u).map n
      (HomotopyPushout.cylinder
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)) n (lower t, x)) =
    (HomotopyPushout.inl
      (boundedFlatPerfectPrespectrumMap (polynomialProjection P b))
      (boundedFlatPerfectPrespectrumMap (polynomialProjection P b))).map n
        ((boundedFlatCoefficientPolynomialSquareHomotopy P u).level n (t, x)) :=
  HomotopyPushout.mapOfHomotopies_lower_cell _ _ _ _ _ _ _ _ _ n t x

theorem span_middle (n : ℕ) (t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    (boundedFlatCoefficientPolynomialSpanMap P u).map n
      (HomotopyPushout.cylinder
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)) n (upper (lower t), x)) =
    HomotopyPushout.cylinder
      (boundedFlatPerfectPrespectrumMap (polynomialProjection P b))
      (boundedFlatPerfectPrespectrumMap (polynomialProjection P b)) n
        (t, (boundedFlatPerfectPrespectrumMap (coefficientMap P u)).map n x) :=
  HomotopyPushout.mapOfHomotopies_middle_cell _ _ _ _ _ _ _ _ _ n t x

theorem span_upper (n : ℕ) (t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    (boundedFlatCoefficientPolynomialSpanMap P u).map n
      (HomotopyPushout.cylinder
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)) n (upper (upper t), x)) =
    (HomotopyPushout.inr
      (boundedFlatPerfectPrespectrumMap (polynomialProjection P b))
      (boundedFlatPerfectPrespectrumMap (polynomialProjection P b))).map n
        ((boundedFlatCoefficientPolynomialSquareHomotopy P u).level n (unitInterval.symm t, x)) :=
  HomotopyPushout.mapOfHomotopies_upper_cell _ _ _ _ _ _ _ _ _ n t x

/-- The first whole cell of the original H1 surface has the first component's exact family value. -/
theorem first_native (n : ℕ) (s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (BassH1Components.firstSimplex P u v) n
      (BassH0Diagram.parameter (s, t), x) =
    (boundedFlatCoefficientBassCompositeComparison P u v).level n
      (lower s, HomotopyPushout.cylinder
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)) n (t, x)) :=
  (BassH1Components.first_native P u v n s t x).trans (first_half P u v n s t x).symm

/-- The positive product cell is the actual original H1 value on its complete rectangular region. -/
theorem plus_native (n : ℕ) (s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (BassH1Components.chartProduct P u v (underToLaurent R)) n
      (BassH1Components.plusParameter.{u} (s, t), x) =
    (boundedFlatCoefficientBassCompositeComparison P u v).level n
      (upper s, HomotopyPushout.cylinder
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)) n (lower t, x)) := by
  rw [BassH1Components.plus_native, second_half, span_lower]
  exact (boundedFlatCoefficientBassComparisonHomotopy_inl P v n s _).symm

/-- The middle product-coordinate cell retains the whole original target pushout cylinder. -/
theorem middle_native (n : ℕ) (s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (BassH1Components.middleSimplex P u v) n
      (BassH0Diagram.parameter (s, t), x) =
    (boundedFlatCoefficientBassCompositeComparison P u v).level n
      (upper s, HomotopyPushout.cylinder
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)) n (upper (lower t), x)) := by
  rw [BassH1Components.middle_native, second_half, span_middle]

/-- The inverse product cell retains the original final quarter and its genuine reversed square. -/
theorem minus_native (n : ℕ) (s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (BassH1Components.chartProduct P u v (underToLaurentInvert R)) n
      (BassH1Components.minusParameter.{u} (s, t), x) =
    (boundedFlatCoefficientBassCompositeComparison P u v).level n
      (upper s, HomotopyPushout.cylinder
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)) n (upper (upper t), x)) := by
  rw [BassH1Components.minus_native, second_half, span_upper]
  exact (boundedFlatCoefficientBassComparisonHomotopy_inr P v n s _).symm

/-- These four parameter charts cover every original H1 point, including all shared boundaries. -/
theorem parameter_cover (s t : unitInterval) :
    (∃ r, lower r = s) ∨
    (∃ r z, upper r = s ∧ lower z = t) ∨
    (∃ r z, upper r = s ∧ upper (lower z) = t) ∨
    (∃ r z, upper r = s ∧ upper (upper z) = t) := by
  rcases Quillen.NativePathCells.cover s with hs | ⟨r, hr⟩
  · exact Or.inl hs
  · rcases Quillen.NativePathCells.three_cover t with ⟨z, hz⟩ | ⟨z, hz⟩ | ⟨z, hz⟩
    · exact Or.inr (Or.inl ⟨r, z, hr, hz⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨r, z, hr, hz⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨r, z, hr, hz⟩))

end Quillen.PerfectComplexes.BassH1NativeCells
