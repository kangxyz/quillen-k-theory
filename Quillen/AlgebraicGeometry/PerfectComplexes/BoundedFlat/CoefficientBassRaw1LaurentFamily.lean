/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassLaurentProjectionRouteBridge
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassLaurentProjectionBoundary
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNervePointwiseFamily

/-! The full Laurent summand of the original second-projection comparison. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS CommRingCat.PolynomialLaurent
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassRaw1LaurentFamily
open CoefficientBassLaurentProjectionScalar
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  {a b : Under R} (u : a ⟶ b)

/-- The original bounded-flat perfect prespectrum on the source Laurent coefficient fiber. -/
abbrev input := originalPrespectrum (boundedFlatPerfectWaldhausen
  (space (op P, (laurentUnderFunctor R).obj a)))
/-- The original two-chart Bass cone at the target Laurent coefficient algebra. -/
abbrev output := mappingCone
  (boundedFlatCoefficientBassSquareComparison P ((laurentUnderFunctor R).obj b))

/-- The original Laurent inclusion into the target two-chart Bass cone. -/
def inclusion := mappingConeInclusion
  (boundedFlatCoefficientBassSquareComparison P ((laurentUnderFunctor R).obj b))

/-- Jointly continuous comparison, route and arbitrary Laurent-input family. -/
def nativeFamily (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R) (n : ℕ) :
    C((I × I) × (input P (a := a)).space n, (output P (b := b)).space n) :=
  ((inclusion P (b := b)).map n).comp
    (CommonReferenceNerve.compactPrespectrumFamily (reference P α u) (family P α u) n)

/-- The genuine native basepoint is fixed throughout the full parameter square. -/
theorem nativeFamily_point (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (n : ℕ) (z : I × I) :
    nativeFamily P u α n (z, (input P (a := a)).point n) = (output P (b := b)).point n := by
  exact (congrArg ((inclusion P (b := b)).map n)
    (family_point P α u n z)).trans ((inclusion P (b := b)).map_point n)

/-- Structure time is separate from the comparison and route coordinates. -/
theorem nativeFamily_structure (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (n : ℕ) (z : I × I) (x : (input P (a := a)).space n) (w : I) :
    nativeFamily P u α (n + 1) (z, (input P (a := a)).structureMap n x w) =
      (output P (b := b)).structureMap n (nativeFamily P u α n (z, x)) w := by
  have h := congrArg ((inclusion P (b := b)).map (n + 1))
    (family_structure P α u n z x w)
  exact h.trans (congrArg (fun γ ↦ γ w) ((inclusion P (b := b)).comm n
    (CommonReferenceNerve.compactPrespectrumFamily (reference P α u) (family P α u) n (z, x))))

/-- The entire bottom route edge is fixed, for every original Laurent input. -/
theorem nativeFamily_bottom (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (n : ℕ) (r : I) (x : (input P (a := a)).space n) :
    nativeFamily P u α n ((r, 0), x) = nativeFamily P u α n ((0, 0), x) := by
  have hf := (family_bottom P α u r).trans (family_bottom P α u 0).symm
  have hv := congrArg (fun z ↦
    CommonReferenceNerve.pointwisePrespectrumFamily (reference P α u) n z x) hf
  have h0 := CommonReferenceNerve.pointwisePrespectrumFamily_eq_compact
    (reference P α u) (family P α u) n (r, 0) x
  have h1 := CommonReferenceNerve.pointwisePrespectrumFamily_eq_compact
    (reference P α u) (family P α u) n (0, 0) x
  exact congrArg ((inclusion P (b := b)).map n) (h0.symm.trans (hv.trans h1))

/-- The entire top route edge is fixed, for every original Laurent input. -/
theorem nativeFamily_top (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (n : ℕ) (r : I) (x : (input P (a := a)).space n) :
    nativeFamily P u α n ((r, 1), x) = nativeFamily P u α n ((0, 1), x) := by
  have hf := (family_top P α u r).trans (family_top P α u 0).symm
  have hv := congrArg (fun z ↦
    CommonReferenceNerve.pointwisePrespectrumFamily (reference P α u) n z x) hf
  have h0 := CommonReferenceNerve.pointwisePrespectrumFamily_eq_compact
    (reference P α u) (family P α u) n (r, 1) x
  have h1 := CommonReferenceNerve.pointwisePrespectrumFamily_eq_compact
    (reference P α u) (family P α u) n (0, 1) x
  exact congrArg ((inclusion P (b := b)).map n) (h0.symm.trans (hv.trans h1))

/-- The plus zero cap is the actual old cone route on its entire Laurent summand. -/
theorem plus_zero (n : ℕ) (t : I) (x : (input P (a := a)).space n) :
    nativeFamily P u (underToLaurent R) n ((0, t), x) =
    (CoefficientBassSecondConeProjectionRoutes.plusLeft P u).level n
      (t, (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a)).map n x) := by
  exact (congrArg ((inclusion P (b := b)).map n)
    (CoefficientBassLaurentProjectionScalar.plus_zero_native P u n t x)).trans
      (CoefficientBassLaurentProjectionBoundary.plusLeft_inclusion P u n t x).symm

/-- The plus one cap is the actual old cone route on its entire Laurent summand. -/
theorem plus_one (n : ℕ) (t : I) (x : (input P (a := a)).space n) :
    nativeFamily P u (underToLaurent R) n ((1, t), x) =
    (CoefficientBassSecondConeProjectionRoutes.plusRight P u).level n
      (t, (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a)).map n x) := by
  exact (congrArg ((inclusion P (b := b)).map n)
    (CoefficientBassLaurentProjectionScalar.plus_one_native P u n t x)).trans
      (CoefficientBassLaurentProjectionBoundary.plusRight_inclusion P u n t x).symm

/-- The minus zero cap is the actual old cone route on its entire Laurent summand. -/
theorem minus_zero (n : ℕ) (t : I) (x : (input P (a := a)).space n) :
    nativeFamily P u (underToLaurentInvert R) n ((0, t), x) =
    (CoefficientBassSecondConeProjectionRoutes.minusLeft P u).level n
      (t, (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a)).map n x) := by
  exact (congrArg ((inclusion P (b := b)).map n)
    (CoefficientBassLaurentProjectionScalar.minus_zero_native P u n t x)).trans
      (CoefficientBassLaurentProjectionBoundary.minusLeft_inclusion P u n t x).symm

/-- The minus one cap is the actual old cone route on its entire Laurent summand. -/
theorem minus_one (n : ℕ) (t : I) (x : (input P (a := a)).space n) :
    nativeFamily P u (underToLaurentInvert R) n ((1, t), x) =
    (CoefficientBassSecondConeProjectionRoutes.minusRight P u).level n
      (t, (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a)).map n x) := by
  exact (congrArg ((inclusion P (b := b)).map n)
    (CoefficientBassLaurentProjectionScalar.minus_one_native P u n t x)).trans
      (CoefficientBassLaurentProjectionBoundary.minusRight_inclusion P u n t x).symm

end Quillen.PerfectComplexes.CoefficientBassRaw1LaurentFamily
