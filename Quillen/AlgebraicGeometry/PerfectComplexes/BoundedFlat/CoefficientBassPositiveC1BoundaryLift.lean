/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveC1BoundarySeam
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BinaryNativePath
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveSupportComposition

/-!
# Exact native recovery of the original paused positive C1 boundary

The lower C1BoundarySeam owner supplies the unchanged full-reference carrier seam.
This owner recovers the original binary composition, prescribed paused polynomialComposition,
and whole native chart. All previous public names, types and proof bodies are retained.
The split changes dependency organization only; it removes no native or route obligations.
-/
@[expose] public section
noncomputable section
set_option warningAsError true
set_option linter.mathlibStandardSet true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters Quillen.NativePathCells
open scoped Simplicial Topology unitInterval
universe u

namespace Quillen.PerfectComplexes.CoefficientBassPositiveC1BoundaryLift
open BassH0Merge CommonReferenceNerve
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

private theorem binary_nodes_simplex {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ModelSimplex.ofIsos (BinaryNormalizationSimplex.sourceMap f g)
      (fun i ↦ (binaryNodes f g i).1) (fun i ↦ (binaryNodes f g i).2) =
      BinaryNormalizationSimplex.simplex f g := by
  let Fs : Fin 3 → (modelOf (boundedFlatPerfectWaldhausen Z) ⟶
      modelOf (boundedFlatPerfectWaldhausen X)) :=
    ![BinaryNormalizationSimplex.sourceMap f g, BinaryNormalizationSimplex.intermediateMap f g,
      BinaryNormalizationSimplex.targetMap f g]
  let refs : ∀ i, (BinaryNormalizationSimplex.sourceMap f g).functor ≅ (Fs i).functor :=
    Fin.cases (Iso.refl _) (Fin.cases (BinaryNormalizationSimplex.first f g)
      (Fin.cases (BinaryNormalizationSimplex.total f g) (fun j ↦ Fin.elim0 j)))
  exact ModelSimplex.ofIsos_nodes_congr (binaryNodes f g) (fun i ↦ ⟨Fs i, refs i⟩)
    (by intro i; fin_cases i <;> rfl)

/-- The actual binary row evaluates to the unchanged polynomial composition at every level. -/
theorem polynomial_binary_native (n : ℕ) (r : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumFamily (polynomialReference P u v) (polynomialNodes P u v) n
      (binaryPath (k := 2) 0 1 2 r, x) =
    (boundedFlatCoefficientPolynomialCompositionHomotopy P u v).level n
      (r, (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)).map n x) := by
  unfold polynomialNodes polynomialReference
  rw [prespectrumFamily_precomp, prespectrumFamily_eq, binary_nodes_simplex]
  exact BinaryNormalizationSimplex.native_path _ _ n r _

/-- The complete paused family is the original polynomialComposition, retaining its casts. -/
theorem polynomial_family_native (n : ℕ) (r : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumFamily (polynomialReference P u v) (polynomialNodes P u v) n
      (pausedBinaryParameter r, x) =
    (CoefficientBassPositiveCompositionTrack.polynomialComposition P u v).level n
      (r, (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)).map n x) := by
  rcases cover r with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · rw [pausedBinaryParameter, path_lower,
      CoefficientBassPositiveCompositionTrack.polynomialComposition,
      Quillen.LoopPrespectrum.Homotopy.trans_lower_cell]
    exact polynomial_binary_native P u v n t x
  · rw [pausedBinaryParameter, path_upper,
      CoefficientBassPositiveCompositionTrack.polynomialComposition,
      Quillen.LoopPrespectrum.Homotopy.trans_upper_cell]
    have h := polynomial_binary_native P u v n 1 x
    rw [Path.target] at h
    exact h.trans ((boundedFlatCoefficientPolynomialCompositionHomotopy P u v).at_one n _)

/-- The whole chart retains every original paused coordinate and native input. -/
theorem chart_family_native (n : ℕ) (r s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumFamily (laurentReference P u v) (chartNodes P u v) n
      (DoubleSquareScalarPaths.coefficientPausedSquareParameter (r, s), x) =
    (boundedFlatCoefficientBassCompositionPlusChart P u v).level n
      (r, (s, (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)).map n x)) := by
  rw [prespectrumFamily_eq, BassOverlap.chartOverlap_simplex,
    prespectrumSimplexFamily_precomp]
  exact CoefficientTransformationComposition.Scalar.plusChart_native P u v n r s _

/-- Compact evaluation of the exact polynomial carrier recovers all original native levels. -/
theorem polynomialParameter_native (n : ℕ) (r : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    compactPrespectrumFamily (polynomialReference P u v) (polynomialParameter P u v)
      n (r, x) =
    (CoefficientBassPositiveCompositionTrack.polynomialComposition P u v).level n
      (r, (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)).map n x) :=
  (compactPrespectrumFamily_eq_simplex _ _ (polynomialNodes P u v) r
    (pausedBinaryParameter r) rfl n x).trans (polynomial_family_native P u v n r x)

/-- Compact evaluation of the whole chart keeps both its independent original times. -/
theorem chartParameter_native (n : ℕ) (r s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    compactPrespectrumFamily (laurentReference P u v) (chartParameter P u v)
      n ((r, s), x) =
    (boundedFlatCoefficientBassCompositionPlusChart P u v).level n
      (r, (s, (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)).map n x)) :=
  (compactPrespectrumFamily_eq_simplex _ _ (chartNodes P u v) (r, s)
    (DoubleSquareScalarPaths.coefficientPausedSquareParameter (r, s)) rfl n x).trans
      (chart_family_native P u v n r s x)

end Quillen.PerfectComplexes.CoefficientBassPositiveC1BoundaryLift
