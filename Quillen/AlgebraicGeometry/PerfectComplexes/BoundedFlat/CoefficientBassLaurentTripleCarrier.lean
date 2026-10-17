/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TripleNativeEvaluation
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveCompactFamily
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassCoherence

/-! The original Laurent triple comparison in its own full-reference carrier. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassLaurentTripleCarrier
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  {a b c d : Under R} (p : a ⟶ b) (q : b ⟶ c) (r : c ⟶ d)
local notation "f" => coefficientMap P (CategoryTheory.Functor.map (laurentUnderFunctor R) r)
local notation "g" => coefficientMap P (CategoryTheory.Functor.map (laurentUnderFunctor R) q)
local notation "h" => coefficientMap P (CategoryTheory.Functor.map (laurentUnderFunctor R) p)

/-- The normalized source reference for the three original Laurent coefficient maps. -/
abbrev reference := NormalizedTripleSimplex.sourceMap f g h

/-- The eight full split-triple nodes in that original Laurent source reference. -/
def nodes : Fin 8 → CommonReferenceNerve.Node (reference P p q r) :=
  fun i ↦ ⟨SplitTripleSimplex.vertices f g h i, SplitTripleSimplex.references f g h i⟩

/-- The original split-triple comparison surface in its full Laurent reference nerve. -/
def family : C(I × I, |nerve (Codiscrete (CommonReferenceNerve.Node
    (reference P p q r)))|) :=
  (CommonReferenceNerve.parameter (reference P p q r) (nodes P p q r)).comp
    SplitTripleSimplex.comparisonParameter

theorem family_native (n : ℕ) (s t : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (Opposite.op P, (laurentUnderFunctor R).obj a)))).space n) :
    CommonReferenceNerve.compactPrespectrumFamily (reference P p q r)
      (family P p q r) n ((s, t), x) =
      (boundedFlatTripleTrackComparison f g h).level n (s, (t, x)) := by
  exact (CommonReferenceNerve.compactPrespectrumFamily_eq_simplex
    (reference P p q r) (family P p q r) (nodes P p q r) (s, t)
    (SplitTripleSimplex.comparisonParameter (s, t)) rfl n x).trans
      (by
        rw [CommonReferenceNerve.prespectrumFamily_eq]
        exact SplitTripleSimplex.comparison_native_evaluation f g h n s t x)

/-- The whole source edge is the unchanged pair of binary split tracks. -/
theorem family_zero (t : I) :
    family P p q r (0, t) = CommonReferenceNerve.parameter (reference P p q r)
      (nodes P p q r) (SplitTripleSimplex.splitLeftPath t) :=
  congrArg (CommonReferenceNerve.parameter (reference P p q r) (nodes P p q r))
    (SplitTripleSimplex.comparisonParameter.apply_zero t)

/-- The whole target edge retains the other original binary association. -/
theorem family_one (t : I) :
    family P p q r (1, t) = CommonReferenceNerve.parameter (reference P p q r)
      (nodes P p q r) (SplitTripleSimplex.splitRightPath t) :=
  congrArg (CommonReferenceNerve.parameter (reference P p q r) (nodes P p q r))
    (SplitTripleSimplex.comparisonParameter.apply_one t)

/-- Every comparison time fixes the complete source reference node. -/
theorem family_bottom (s : I) :
    family P p q r (s, 0) = CommonReferenceNerve.parameter (reference P p q r)
      (nodes P p q r) (Convexity.StdSimplex.single 0) :=
  congrArg (CommonReferenceNerve.parameter (reference P p q r) (nodes P p q r))
    (SplitTripleSimplex.comparisonParameter.source s)

/-- Every comparison time fixes the complete terminal reference node. -/
theorem family_top (s : I) :
    family P p q r (s, 1) = CommonReferenceNerve.parameter (reference P p q r)
      (nodes P p q r) (Convexity.StdSimplex.single 7) :=
  congrArg (CommonReferenceNerve.parameter (reference P p q r) (nodes P p q r))
    (SplitTripleSimplex.comparisonParameter.target s)

/-- The family fixes the original native basepoint in every degree. -/
theorem family_point (n : ℕ) (z : I × I) :
    CommonReferenceNerve.compactPrespectrumFamily (reference P p q r)
      (family P p q r) n (z, (prespectrum _).point n) = (prespectrum _).point n :=
  CommonReferenceNerve.compactPrespectrumFamily_point _ _ n z

/-- Structure time is independent of both comparison coordinates. -/
theorem family_structure (n : ℕ) (z : I × I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (Opposite.op P, (laurentUnderFunctor R).obj a)))).space n) (w : I) :
    CommonReferenceNerve.compactPrespectrumFamily (reference P p q r)
      (family P p q r) (n + 1) (z, (prespectrum _).structureMap n x w) =
      (prespectrum _).structureMap n
        (CommonReferenceNerve.compactPrespectrumFamily (reference P p q r)
          (family P p q r) n (z, x)) w :=
  CommonReferenceNerve.compactPrespectrumFamily_structure _ _ n z x w

end Quillen.PerfectComplexes.CoefficientBassLaurentTripleCarrier
