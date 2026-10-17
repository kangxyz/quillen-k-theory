/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveC1SourceProductStrips
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveC0UnitNative
public import Quillen.Waldhausen.SConstruction.Iterated.RealizationSimplexComposition
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveReanchorFamily

/-! Exact native product evaluation of the original source-positive and source-unit strips. -/
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
namespace Quillen.PerfectComplexes.CoefficientBassPositiveC1SourceProductNative
open CommonReferenceNerve CoefficientBassPositiveC1SourceUnitProduct
open CoefficientBassPositiveC1SourceProductStrips CoefficientBassPositiveC0UnitStrip
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- Only the common reference changes in the actual nine-node product diagram. -/
theorem positive_original :
    ModelSimplex.ofIsos (BassOverlap.commonReference P p q)
      (fun i ↦ (positiveNineNodes P p q i).1) (fun i ↦ (positiveNineNodes P p q i).2) =
    CommonReferenceProduct.simplex (BassProjectionPath.source P a)
      (fun i ↦ (BassH0Merge.binaryNodes (laurentPlus P a) (polynomialProjection P a) i).1)
      (fun i ↦ (BassH0Merge.binaryNodes (laurentPlus P a) (polynomialProjection P a) i).2)
      (BassLaurentBottomFace.source P p q) (BassLaurentBottomFace.vertices P p q)
      (BassLaurentBottomFace.references P p q) :=
  ModelSimplex.ofIsos_change_reference (BassBottomCommonFamily.referenceIso P p q) _ _

/-- The six-node source-unit product retains the identical bottom anchor. -/
theorem unit_original :
    ModelSimplex.ofIsos (BassOverlap.commonReference P p q)
      (fun i ↦ (unitSixNodes P p q i).1) (fun i ↦ (unitSixNodes P p q i).2) =
    CommonReferenceProduct.simplex (BassProjectionPath.source P a)
      (fun i ↦ (unitNodes P a i).1) (fun i ↦ (unitNodes P a i).2)
      (BassLaurentBottomFace.source P p q) (BassLaurentBottomFace.vertices P p q)
      (BassLaurentBottomFace.references P p q) :=
  ModelSimplex.ofIsos_change_reference (BassBottomCommonFamily.referenceIso P p q) _ _

private theorem binary_simplex {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ModelSimplex.ofIsos (BinaryNormalizationSimplex.sourceMap f g)
      (fun i ↦ (BassH0Merge.binaryNodes f g i).1)
      (fun i ↦ (BassH0Merge.binaryNodes f g i).2) =
        BinaryNormalizationSimplex.simplex f g := by
  unfold BinaryNormalizationSimplex.simplex
  apply ModelSimplex.ext_diagram
  refine CategoryTheory.Functor.hext (fun i ↦ ?_) ?_
  · fin_cases i <;> rfl
  · intro i j h
    fin_cases i <;> fin_cases j <;> rfl

/-- The source-positive binary family is the original cast positive track, without reversal. -/
theorem positive_binary_native (n : ℕ) (s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (ModelSimplex.ofIsos (BassProjectionPath.source P a)
      (fun i ↦ (BassH0Merge.binaryNodes (laurentPlus P a) (polynomialProjection P a) i).1)
      (fun i ↦ (BassH0Merge.binaryNodes (laurentPlus P a) (polynomialProjection P a) i).2))
      n (binaryPath (k := 2) 0 1 2 s, x) =
        (boundedFlatCoefficientLaurentPlusHomotopy P a).level n (s, x) := by
  rw [boundedFlatCoefficientLaurentPlusHomotopy,
    Quillen.LoopPrespectrum.Homotopy.cast_level]
  change prespectrumSimplexFamily
    (ModelSimplex.ofIsos (BinaryNormalizationSimplex.sourceMap
      (laurentPlus P a) (polynomialProjection P a))
      (fun i ↦ (BassH0Merge.binaryNodes (laurentPlus P a) (polynomialProjection P a) i).1)
      (fun i ↦ (BassH0Merge.binaryNodes (laurentPlus P a) (polynomialProjection P a) i).2))
    n (binaryPath (k := 2) 0 1 2 s, x) = _
  rw [binary_simplex]
  exact BinaryNormalizationSimplex.native_path
    (laurentPlus P a) (polynomialProjection P a) n s x

/-- The full positive product evaluates in source-first order at all original levels. -/
theorem positive_family (n : ℕ) (r s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumFamily (BassOverlap.commonReference P p q) (positiveNineNodes P p q) n
      (SimplexGrid.parameter.{u + 1} 2 2
        (binaryPath (k := 2) 0 1 2 s, binaryPath (k := 2) 0 1 2 r), x) =
      (boundedFlatCoefficientLaurentCompositionHomotopy P p q).level n
        (r, (boundedFlatCoefficientLaurentPlusHomotopy P a).level n (s, x)) := by
  rw [prespectrumFamily_eq, positive_original]
  refine (CommonReferenceProduct.prespectrum_comp.{u + 1}
    (BassProjectionPath.source P a)
    (fun i ↦ (BassH0Merge.binaryNodes (laurentPlus P a) (polynomialProjection P a) i).1)
    (fun i ↦ (BassH0Merge.binaryNodes (laurentPlus P a) (polynomialProjection P a) i).2)
    (BassLaurentBottomFace.source P p q) (BassLaurentBottomFace.vertices P p q)
    (BassLaurentBottomFace.references P p q) n x
    (binaryPath (k := 2) 0 1 2 s) (binaryPath (k := 2) 0 1 2 r)).trans ?_
  rw [positive_binary_native, BassLaurentBottomFace.laurent_native]

/-- The source-unit product evaluates the actual beta-conjugated unit before composition. -/
theorem unit_family (n : ℕ) (r s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumFamily (BassOverlap.commonReference P p q) (unitSixNodes P p q) n
      (SimplexGrid.parameter.{u + 1} 1 2
        (edge (k := 1) 0 1 s, binaryPath (k := 2) 0 1 2 r), x) =
      (boundedFlatCoefficientLaurentCompositionHomotopy P p q).level n
        (r, (boundedFlatCoefficientLaurentUnitHomotopy P a).level n (s, x)) := by
  rw [prespectrumFamily_eq, unit_original]
  refine (CommonReferenceProduct.prespectrum_comp.{u + 1}
    (BassProjectionPath.source P a) (fun i ↦ (unitNodes P a i).1)
    (fun i ↦ (unitNodes P a i).2) (BassLaurentBottomFace.source P p q)
    (BassLaurentBottomFace.vertices P p q) (BassLaurentBottomFace.references P p q) n x
    (edge (k := 1) 0 1 s) (binaryPath (k := 2) 0 1 2 r)).trans ?_
  rw [CoefficientBassPositiveC0UnitNative.splitUnit_native, BassLaurentBottomFace.laurent_native]

/-- Compact positive evaluation retains composition time, positive time and the whole input. -/
theorem positiveParameter_native (n : ℕ) (r s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    compactPrespectrumFamily (BassOverlap.commonReference P p q) (positiveParameter P p q)
      n ((r, s), x) =
      (boundedFlatCoefficientLaurentCompositionHomotopy P p q).level n
        (r, (boundedFlatCoefficientLaurentPlusHomotopy P a).level n (s, x)) :=
  (compactPrespectrumFamily_eq_simplex _ _ (positiveNineNodes P p q) (r, s)
    (SimplexGrid.parameter.{u + 1} 2 2
      (binaryPath (k := 2) 0 1 2 s, binaryPath (k := 2) 0 1 2 r)) rfl n x).trans
    (positive_family P p q n r s x)

/-- Compact unit evaluation retains its independent forward unit time, also at degree zero. -/
theorem unitParameter_native (n : ℕ) (r s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    compactPrespectrumFamily (BassOverlap.commonReference P p q) (unitParameter P p q)
      n ((r, s), x) =
      (boundedFlatCoefficientLaurentCompositionHomotopy P p q).level n
        (r, (boundedFlatCoefficientLaurentUnitHomotopy P a).level n (s, x)) :=
  (compactPrespectrumFamily_eq_simplex _ _ (unitSixNodes P p q) (r, s)
    (SimplexGrid.parameter.{u + 1} 1 2
      (edge (k := 1) 0 1 s, binaryPath (k := 2) 0 1 2 r)) rfl n x).trans
    (unit_family P p q n r s x)

/-- The distinct shifted positive family has the same native values by full reference action. -/
theorem shiftedPositiveParameter_native (n : ℕ) (r s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    compactPrespectrumFamily (BassOverlap.commonReference P p q)
      (shiftedPositiveParameter P p q) n ((r, s), x) =
      (boundedFlatCoefficientLaurentCompositionHomotopy P p q).level n
        (r, (boundedFlatCoefficientLaurentPlusHomotopy P a).level n (s, x)) := by
  have hp : shiftedPositiveParameter P p q (r, s) =
      parameter (BassOverlap.commonReference P p q)
        (fun i ↦ CommonReferenceProduct.reanchor
          (LaurentUnitReferenceSpecialization.commonUnit P p q) (positiveNineNodes P p q i))
        (SimplexGrid.parameter.{u + 1} 2 2
          (binaryPath (k := 2) 0 1 2 s, binaryPath (k := 2) 0 1 2 r)) :=
    mapParameter_parameter _ _ _
  refine (compactPrespectrumFamily_eq_simplex _ _ _ (r, s) _ hp n x).trans ?_
  change prespectrumFamily _ (ModelSimplex.reanchorNodes
    (LaurentUnitReferenceSpecialization.commonUnit P p q) (positiveNineNodes P p q)) n _ = _
  rw [prespectrumFamily_reanchor]
  exact positive_family P p q n r s x

end Quillen.PerfectComplexes.CoefficientBassPositiveC1SourceProductNative
