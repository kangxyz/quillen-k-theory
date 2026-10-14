/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassMergedBoundarySimplex

/-! The actual original chart/bottom scalar boundary is shared in the merged family. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity
open Quillen.PolynomialBaseChange Quillen.Scheme.CoefficientBaseChange
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassReferenceMerge

/-- The original positive chart parameter, embedded through the entire retained chart diagram. -/
def plusParameter : C(unitInterval × unitInterval, StdSimplex ℝ (Fin 45)) :=
  ⟨fun z ↦ StdSimplex.map chartFace.toOrderHom
    (StdSimplex.map BassOverlap.plusFace.toOrderHom
      (DoubleSquareScalarPaths.coefficientPausedSquareParameter z)), by fun_prop⟩

/-- The original inverse chart parameter, with its original collapse and pause. -/
def minusParameter : C(unitInterval × unitInterval, StdSimplex ℝ (Fin 45)) :=
  ⟨fun z ↦ StdSimplex.map chartFace.toOrderHom
    (StdSimplex.map BassOverlap.minusFace.toOrderHom
      (DoubleSquareScalarPaths.coefficientPausedSquareParameter z)), by fun_prop⟩

/-- The actual Laurent-composition bottom parameter, using the genuine realization product. -/
def bottomParameter : C(unitInterval × unitInterval, StdSimplex ℝ (Fin 45)) :=
  ⟨fun z ↦ StdSimplex.map bottomFace.toOrderHom (BassLaurentBottomFace.parameter.{u} z),
    by fun_prop⟩

/-- The entire positive shared edge is equal in scalar coordinates. -/
theorem plus_bottom_scalar (r : unitInterval) :
    plusParameter (r, 0) = bottomParameter.{u} (r, 0) := by
  change StdSimplex.map chartFace.toOrderHom
    (StdSimplex.map BassOverlap.plusFace.toOrderHom
      (DoubleSquareScalarPaths.coefficientPausedSquareParameter (r, 0))) =
    StdSimplex.map bottomFace.toOrderHom (BassLaurentBottomFace.parameter (r, 0))
  rw [BassOverlap.plus_lower_parameter, BassLaurentBottomFace.parameter_left]
  trans binaryPath (k := 44) 21 22 23 r
  · exact map_binaryPath chartFace 15 16 17 r
  · exact (map_binaryPath bottomFace 6 7 8 r).symm

/-- Equality of the separate inverse shared edge, retaining its complete original path. -/
theorem minus_bottom_scalar (r : unitInterval) :
    minusParameter (r, 0) = bottomParameter.{u} (r, 1) := by
  change StdSimplex.map chartFace.toOrderHom
    (StdSimplex.map BassOverlap.minusFace.toOrderHom
      (DoubleSquareScalarPaths.coefficientPausedSquareParameter (r, 0))) =
    StdSimplex.map bottomFace.toOrderHom (BassLaurentBottomFace.parameter (r, 1))
  rw [BassOverlap.minus_lower_parameter, BassLaurentBottomFace.parameter_right]
  trans binaryPath (k := 44) 42 43 44 r
  · exact map_binaryPath chartFace 33 34 35 r
  · exact (map_binaryPath bottomFace 12 13 14 r).symm

variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- The complete fixed original positive chart survives the dependent-node merge pointwise. -/
theorem plus_native (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P u v) n (plusParameter (r, s), x) =
      (boundedFlatCoefficientBassCompositionPlusChart P u v).level n
        (r, (s, (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)).map n x)) := by
  change prespectrumSimplexFamily (simplex P u v) n
    (StdSimplex.map chartFace.toOrderHom _, x) = _
  rw [prespectrumSimplexFamily_face, chart_face]
  exact BassOverlap.plusChart_native P u v n r s x

/-- The complete fixed original inverse chart survives the same merge pointwise. -/
theorem minus_native (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P u v) n (minusParameter (r, s), x) =
      (boundedFlatCoefficientBassCompositionMinusChart P u v).level n
        (r, (s, (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)).map n x)) := by
  change prespectrumSimplexFamily (simplex P u v) n
    (StdSimplex.map chartFace.toOrderHom _, x) = _
  rw [prespectrumSimplexFamily_face, chart_face]
  exact BassOverlap.minusChart_native P u v n r s x

/-- The full prescribed original bottom surface survives, with both times independent. -/
theorem bottom_native (n : ℕ) (r t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P u v) n (bottomParameter.{u} (r, t), x) =
      (Quillen.LoopPrespectrum.Homotopy.precomp (boundedFlatCoefficientBassSquareComparison P a)
        (boundedFlatCoefficientLaurentCompositionHomotopy P u v)).level n
        (r, Quillen.LoopPrespectrum.HomotopyPushout.cylinder
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)) n (t, x)) := by
  change prespectrumSimplexFamily (simplex P u v) n
    (StdSimplex.map bottomFace.toOrderHom _, x) = _
  rw [prespectrumSimplexFamily_face, bottom_face]
  exact BassLaurentBottomFace.native P u v n r t x

/-- The merged family fixes the original point for every scalar parameter. -/
theorem family_point (n : ℕ) (z : StdSimplex ℝ (Fin 45)) :
    prespectrumSimplexFamily (simplex P u v) n
      (z, (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).point n) =
      (originalPrespectrum (boundedFlatPerfectWaldhausen
        (space (op P, (laurentUnderFunctor R).obj c)))).point n :=
  prespectrumSimplexFamily_point (simplex P u v) n z

/-- The native structure parameter remains independent of the entire merged scalar family. -/
theorem family_structure (n : ℕ) (z : StdSimplex ℝ (Fin 45))
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n)
    (t : unitInterval) :
    prespectrumSimplexFamily (simplex P u v) (n + 1)
      (z, (originalPrespectrum
        (boundedFlatPerfectWaldhausen (space (op P, a)))).structureMap n x t) =
    (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (laurentUnderFunctor R).obj c)))).structureMap n
        (prespectrumSimplexFamily (simplex P u v) n (z, x)) t :=
  prespectrumSimplexFamily_structure (simplex P u v) n z x t

end Quillen.PerfectComplexes.BassReferenceMerge
