/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ProjectionRectangleSquareRows

/-! Named semantic consumers of the actual whole original reference families. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option linter.mathlibStandardSet true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity
open Quillen Quillen.PerfectComplexes
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters Quillen.NativePathCells
open scoped Simplicial Topology unitInterval
universe u
open Quillen.PerfectComplexes.ProjectionRectangleSquareRows BassH0Merge BassH1Join
  BassReferenceMerge
namespace QuillenTest.ProjectionRectangleSquareRows
variable {A B C A' B' C' : Scheme.{u}}
  (p : B ⟶ A) (q : C ⟶ B) (p' : B' ⟶ A') (q' : C' ⟶ B')
  (a : A' ⟶ A) (b : B' ⟶ B) (c : C' ⟶ C)
  (hp : b ≫ p = p' ≫ a) (hq : c ≫ q = q' ≫ b)
  (r : C ⟶ A) (hr : q ≫ p = r)


/-- The named consumer retains every original parameter and full dependent reference. -/
theorem original_chart_nerve_parameter (t : unitInterval) :
    CommonReferenceNerve.parameter (ProjectionReference.reference c r) (ProjectionReference.nodes
      p q p' q' a b c hp hq r hr)
      (StdSimplex.map chartRow (NativeSquareFiveSimplex.parameter t)) =
    CommonReferenceNerve.parameter (ProjectionReference.reference c r) (fun i ↦ preReferenceNode
      (ProjectionReference.reference c r) (normalizedMap p)
        (chartAnchor p q c r hr) (NativeSquareFiveSimplex.nodes c q q' b hq i))
      (NativeSquareFiveSimplex.parameter t) := by
  apply ProjectionRectangleSquareRows.chart_nerve_parameter

/-- The named consumer retains every original parameter and full dependent reference. -/
theorem original_chart_row_family (n : ℕ) (z : StdSimplex ℝ (Fin 5))
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen A))).space n) :
    CommonReferenceNerve.prespectrumFamily (ProjectionReference.reference c r)
      (fun i ↦ ProjectionReference.nodes p q p' q' a b c hp hq r hr (chartRow i)) n (z, x) =
    CommonReferenceNerve.prespectrumFamily (ProjectionReference.reference c r) (fun i ↦
      preReferenceNode (ProjectionReference.reference c r) (normalizedMap p)
        (chartAnchor p q c r hr) (NativeSquareFiveSimplex.nodes c q q' b hq i)) n (z, x) := by
  apply ProjectionRectangleSquareRows.chart_row_family

/-- The named consumer retains every original parameter and full dependent reference. -/
theorem original_chart_row_point (n : ℕ) (t : unitInterval) :
    CommonReferenceNerve.prespectrumFamily (ProjectionReference.reference c r) (fun i ↦
      preReferenceNode (ProjectionReference.reference c r) (normalizedMap p)
        (chartAnchor p q c r hr) (NativeSquareFiveSimplex.nodes c q q' b hq i)) n
      (NativeSquareFiveSimplex.parameter t,
        (prespectrum (modelOf (boundedFlatPerfectWaldhausen A))).point n) =
      (prespectrum (modelOf (boundedFlatPerfectWaldhausen C'))).point n := by
  apply ProjectionRectangleSquareRows.chart_row_point

/-- The named consumer retains every original parameter and full dependent reference. -/
theorem original_chart_row_structure (n : ℕ) (s t : unitInterval)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen A))).space n) :
    CommonReferenceNerve.prespectrumFamily (ProjectionReference.reference c r) (fun i ↦
      preReferenceNode (ProjectionReference.reference c r) (normalizedMap p)
        (chartAnchor p q c r hr) (NativeSquareFiveSimplex.nodes c q q' b hq i)) (n + 1)
      (NativeSquareFiveSimplex.parameter s,
        (prespectrum (modelOf (boundedFlatPerfectWaldhausen A))).structureMap n x t) =
    (prespectrum (modelOf (boundedFlatPerfectWaldhausen C'))).structureMap n
      (CommonReferenceNerve.prespectrumFamily (ProjectionReference.reference c r) (fun i ↦
        preReferenceNode (ProjectionReference.reference c r) (normalizedMap p)
        (chartAnchor p q c r hr) (NativeSquareFiveSimplex.nodes c q q' b hq i)) n
        (NativeSquareFiveSimplex.parameter s, x)) t := by
  apply ProjectionRectangleSquareRows.chart_row_structure

/-- The named consumer retains every original parameter and full dependent reference. -/
theorem original_polynomial_nerve_parameter (t : unitInterval) :
    CommonReferenceNerve.parameter (ProjectionReference.reference c r) (ProjectionReference.nodes
      p q p' q' a b c hp hq r hr)
      (StdSimplex.map polynomialRow (NativeSquareFiveSimplex.parameter t)) =
    CommonReferenceNerve.parameter (ProjectionReference.reference c r) (fun i ↦ postReferenceNode
      (ProjectionReference.reference c r) (normalizedMap q')
        (polynomialAnchor p q q' b c hq r hr) (NativeSquareFiveSimplex.nodes b p p' a hp i))
      (NativeSquareFiveSimplex.parameter t) := by
  apply ProjectionRectangleSquareRows.polynomial_nerve_parameter

/-- The named consumer retains every original parameter and full dependent reference. -/
theorem original_polynomial_row_family (n : ℕ) (z : StdSimplex ℝ (Fin 5))
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen A))).space n) :
    CommonReferenceNerve.prespectrumFamily (ProjectionReference.reference c r)
      (fun i ↦ ProjectionReference.nodes p q p' q' a b c hp hq r hr (polynomialRow i)) n (z, x) =
    CommonReferenceNerve.prespectrumFamily (ProjectionReference.reference c r) (fun i ↦
      postReferenceNode (ProjectionReference.reference c r) (normalizedMap q')
        (polynomialAnchor p q q' b c hq r hr) (NativeSquareFiveSimplex.nodes b p p' a hp i)) n (z,
          x) := by
  apply ProjectionRectangleSquareRows.polynomial_row_family

/-- The named consumer retains every original parameter and full dependent reference. -/
theorem original_polynomial_row_point (n : ℕ) (t : unitInterval) :
    CommonReferenceNerve.prespectrumFamily (ProjectionReference.reference c r) (fun i ↦
      postReferenceNode (ProjectionReference.reference c r) (normalizedMap q')
        (polynomialAnchor p q q' b c hq r hr) (NativeSquareFiveSimplex.nodes b p p' a hp i)) n
      (NativeSquareFiveSimplex.parameter t,
        (prespectrum (modelOf (boundedFlatPerfectWaldhausen A))).point n) =
      (prespectrum (modelOf (boundedFlatPerfectWaldhausen C'))).point n := by
  apply ProjectionRectangleSquareRows.polynomial_row_point

/-- The named consumer retains every original parameter and full dependent reference. -/
theorem original_polynomial_row_structure (n : ℕ) (s t : unitInterval)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen A))).space n) :
    CommonReferenceNerve.prespectrumFamily (ProjectionReference.reference c r) (fun i ↦
      postReferenceNode (ProjectionReference.reference c r) (normalizedMap q')
        (polynomialAnchor p q q' b c hq r hr) (NativeSquareFiveSimplex.nodes b p p' a hp i)) (n + 1)
      (NativeSquareFiveSimplex.parameter s,
        (prespectrum (modelOf (boundedFlatPerfectWaldhausen A))).structureMap n x t) =
    (prespectrum (modelOf (boundedFlatPerfectWaldhausen C'))).structureMap n
      (CommonReferenceNerve.prespectrumFamily (ProjectionReference.reference c r) (fun i ↦
        postReferenceNode (ProjectionReference.reference c r) (normalizedMap q')
        (polynomialAnchor p q q' b c hq r hr) (NativeSquareFiveSimplex.nodes b p p' a hp i)) n
        (NativeSquareFiveSimplex.parameter s, x)) t := by
  apply ProjectionRectangleSquareRows.polynomial_row_structure

end QuillenTest.ProjectionRectangleSquareRows
