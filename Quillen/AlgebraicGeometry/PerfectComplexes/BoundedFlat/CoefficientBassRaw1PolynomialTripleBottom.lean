/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialRadialLowerFaces

/-! The original split-triple surface in the genuine polynomial triple sheet. -/
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
namespace Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialTripleBottom
open CommonReferenceNerve BassH0Merge
open CoefficientBassRaw1PolynomialTripleAnchor CoefficientBassRaw1PolynomialTripleLowerFaces
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  (β : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  {a b c d : Under R} (p : a ⟶ b) (q : b ⟶ c) (w : c ⟶ d)

/-- All eight original nodes retain the chart-precomposed full Laurent reference. -/
def nodes (i : Fin 8) : Node (polynomialReference P p q w ≫ normalizedMap (chart P β d)) :=
  CommonReferenceProduct.reanchor (referenceIso P β p q w).symm
    (precompNode (normalizedMap (chart P β a)) (tripleNodes P p q w i))

/-- The original simplex is included into this same first sheet. -/
def simplex : C(StdSimplex ℝ (Fin 8), CoefficientBassRaw1PolynomialPostcomp.carrier P p q w β) :=
  (CoefficientBassRaw1PolynomialCapLowerFaces.tripleLaurent P β p q w).comp
    (parameter (polynomialReference P p q w ≫ normalizedMap (chart P β d)) (nodes P β p q w))

/-- The prescribed split-triple homotopy is retained before any carrier extension. -/
def family : C(I × I, CoefficientBassRaw1PolynomialPostcomp.carrier P p q w β) :=
  (simplex P β p q w).comp SplitTripleSimplex.comparisonParameter.toHomotopy.toContinuousMap

/-- The left boundary is the original two-by-two split path. -/
theorem family_zero (s : I) : family P β p q w (0, s) =
    simplex P β p q w (SplitTripleSimplex.splitLeftPath s) :=
  congrArg (simplex P β p q w) (SplitTripleSimplex.comparisonParameter.apply_zero s)

/-- The right boundary retains its separate two original binary comparisons. -/
theorem family_one (s : I) : family P β p q w (1, s) =
    simplex P β p q w (SplitTripleSimplex.splitRightPath s) :=
  congrArg (simplex P β p q w) (SplitTripleSimplex.comparisonParameter.apply_one s)

/-- The complete source vertex is fixed along the original comparison time. -/
theorem family_source (r : I) : family P β p q w (r, 0) =
    simplex P β p q w (StdSimplex.single 0) :=
  congrArg (simplex P β p q w) (SplitTripleSimplex.comparisonParameter.source r)

/-- The complete terminal vertex is fixed along the original comparison time. -/
theorem family_target (r : I) : family P β p q w (r, 1) =
    simplex P β p q w (StdSimplex.single 7) :=
  congrArg (simplex P β p q w) (SplitTripleSimplex.comparisonParameter.target r)

end Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialTripleBottom
