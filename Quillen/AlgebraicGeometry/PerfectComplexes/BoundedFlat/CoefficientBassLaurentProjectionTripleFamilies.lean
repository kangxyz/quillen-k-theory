/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassLaurentTripleCanonicalFamily

/-! Three prescribed Laurent associativity squares in one complete reference. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
open Quillen.Waldhausen.IteratedS CommRingCat.PolynomialLaurent
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassLaurentProjectionTripleFamilies
open BassReferenceMerge BassMWholeNerve
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  {a b : Under R} (u : a ⟶ b)

/-- The coefficient arrow that applies the polynomial coefficient, then `α`, then Laurent `u`. -/
abbrev firstArrow := (((polynomialUnderCoefficient R).app a ≫ α.app a) ≫
  (laurentUnderFunctor R).map u)
/-- The coefficient arrow that applies the polynomial coefficient, then polynomial `u`, then `α`. -/
abbrev secondArrow := (((polynomialUnderCoefficient R).app a ≫
  (polynomialUnderFunctor R).map u) ≫ α.app b)
/-- The coefficient arrow that applies `u`, then the polynomial coefficient, then `α`. -/
abbrev thirdArrow := ((u ≫ (polynomialUnderCoefficient R).app b) ≫ α.app b)

/-- The first common-reference identification is exactly the selected chart naturality. -/
theorem first_second : firstArrow α u = secondArrow α u :=
  (Category.assoc _ _ _).trans ((congrArg
    (fun k ↦ (polynomialUnderCoefficient R).app a ≫ k) (α.naturality u).symm).trans
      (Category.assoc _ _ _).symm)

/-- The second common-reference identification is exactly polynomial coefficient naturality. -/
theorem second_third : secondArrow α u = thirdArrow α u :=
  congrArg (fun k ↦ k ≫ α.app b) ((polynomialUnderCoefficient R).naturality u).symm

/-- The coefficient reference for the Laurent image of `firstArrow α u`. -/
abbrev reference := coefficientModel P ((laurentUnderFunctor R).map (firstArrow α u))

/-- Identify the first and second coefficient references by chart naturality. -/
def secondAnchor : (reference P α u).functor ≅
    (coefficientModel P ((laurentUnderFunctor R).map (secondArrow α u))).functor :=
  eqToIso (congrArg (fun k ↦ (coefficientModel P ((laurentUnderFunctor R).map k)).functor)
    (first_second α u))

/-- Identify the first and third coefficient references by chart and coefficient naturality. -/
def thirdAnchor : (reference P α u).functor ≅
    (coefficientModel P ((laurentUnderFunctor R).map (thirdArrow α u))).functor :=
  eqToIso (congrArg (fun k ↦ (coefficientModel P ((laurentUnderFunctor R).map k)).functor)
    ((first_second α u).trans (second_third α u)))

/-- The first original triple has no change of its specified scalar clock. -/
def first : C(I × I, |nerve (Codiscrete (CommonReferenceNerve.Node (reference P α u)))|) :=
  CoefficientBassLaurentTripleCanonicalFamily.family P
    ((polynomialUnderCoefficient R).app a) (α.app a) ((laurentUnderFunctor R).map u)

/-- The second original triple is moved by the full chart-square reference equation. -/
def second : C(I × I, |nerve (Codiscrete (CommonReferenceNerve.Node (reference P α u)))|) :=
  (CommonReferenceNerve.mapParameter (CommonReferenceProduct.reanchor (secondAnchor P α u))).comp
    (CoefficientBassLaurentTripleCanonicalFamily.family P
      ((polynomialUnderCoefficient R).app a) ((polynomialUnderFunctor R).map u) (α.app b))

/-- The third original triple is moved by both prescribed reference equalities. -/
def third : C(I × I, |nerve (Codiscrete (CommonReferenceNerve.Node (reference P α u)))|) :=
  (CommonReferenceNerve.mapParameter (CommonReferenceProduct.reanchor (thirdAnchor P α u))).comp
    (CoefficientBassLaurentTripleCanonicalFamily.family P
      u ((polynomialUnderCoefficient R).app b) (α.app b))

end Quillen.PerfectComplexes.CoefficientBassLaurentProjectionTripleFamilies
