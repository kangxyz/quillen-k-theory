/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassLaurentProjectionScalar
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.DoubleSquareRectangleFaces

/-! Native boundary values of the full Laurent parameter surface. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open Quillen.Waldhausen.IteratedS CommRingCat.PolynomialLaurent
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassLaurentProjectionScalar
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  {a b : Under R} (u : a ⟶ b)

/-- The complete initial parameter edge is the original two geometric square tracks. -/
theorem family_zero_original (n : ℕ) (t : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (laurentUnderFunctor R).obj a)))).space n) :
    CommonReferenceNerve.compactPrespectrumFamily (reference P α u) (family P α u)
      n ((0, t), x) =
    (DoubleSquareTrack.originalLeft (p P (a := a)) (q P α (a := a))
      (p' P (b := b)) (q' P α (b := b)) (aMap P u) (bMap P u) (cMap P u)
      (polynomial_square P u) (chart_square P α u)).level n (t, x) := by
  refine (CommonReferenceNerve.compactPrespectrumFamily_eq_simplex
    (reference P α u) (family P α u) (nodes P α u) (0, t) (leftWord t)
    (family_zero P α u t) n x).trans ?_
  rw [CommonReferenceNerve.prespectrumFamily_eq]
  exact DoubleSquareScalarPaths.rectangle_source_original
    (p P (a := a)) (q P α (a := a)) (p' P (b := b)) (q' P α (b := b))
    (aMap P u) (bMap P u) (cMap P u) (polynomial_square P u) (chart_square P α u) n t x

/-- The complete final parameter edge is the original source, outer and target track word. -/
theorem family_one_original (n : ℕ) (t : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (laurentUnderFunctor R).obj a)))).space n) :
    CommonReferenceNerve.compactPrespectrumFamily (reference P α u) (family P α u)
      n ((1, t), x) =
    (DoubleSquareTrack.originalRight (p P (a := a)) (q P α (a := a))
      (p' P (b := b)) (q' P α (b := b)) (aMap P u) (bMap P u) (cMap P u)
      (polynomial_square P u) (chart_square P α u)).level n (t, x) := by
  refine (CommonReferenceNerve.compactPrespectrumFamily_eq_simplex
    (reference P α u) (family P α u) (nodes P α u) (1, t) (rightWord t)
    (family_one P α u t) n x).trans ?_
  rw [CommonReferenceNerve.prespectrumFamily_eq]
  exact DoubleSquareScalarPaths.rectangle_target_original
    (p P (a := a)) (q P α (a := a)) (p' P (b := b)) (q' P α (b := b))
    (aMap P u) (bMap P u) (cMap P u) (polynomial_square P u) (chart_square P α u) n t x

/-- Every comparison and route time fixes the genuine native basepoint. -/
theorem family_point (n : ℕ) (z : I × I) :
    CommonReferenceNerve.compactPrespectrumFamily (reference P α u) (family P α u)
      n (z, (prespectrum _).point n) = (prespectrum _).point n :=
  CommonReferenceNerve.compactPrespectrumFamily_point _ _ n z

/-- The prespectrum structure time remains independent of both parameter coordinates. -/
theorem family_structure (n : ℕ) (z : I × I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (laurentUnderFunctor R).obj a)))).space n) (w : I) :
    CommonReferenceNerve.compactPrespectrumFamily (reference P α u) (family P α u)
      (n + 1) (z, (prespectrum _).structureMap n x w) =
    (prespectrum _).structureMap n
      (CommonReferenceNerve.compactPrespectrumFamily (reference P α u) (family P α u)
        n (z, x)) w :=
  CommonReferenceNerve.compactPrespectrumFamily_structure _ _ n z x w

end Quillen.PerfectComplexes.CoefficientBassLaurentProjectionScalar
