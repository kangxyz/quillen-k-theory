/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveLeftPolynomialParameters
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveWhiskering
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNervePointwiseFamily

/-!
# Native values of the two finite left-route polynomial families

Reference change preserves the original whole square diagrams. Their finite evaluations
therefore give exactly the polynomial p-square postcomposed by q and the polynomial
q-square precomposed by p. Compact-parameter evaluation retains every degree-zero input;
no continuity of a global pointwise evaluator is asserted.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters
open scoped Simplicial Topology unitInterval
universe u

namespace Quillen.PerfectComplexes.CoefficientBassPositiveLeftPolynomialNative
open BassH0Merge BassH1Join CommonReferenceNerve
open CoefficientBassPositiveC1BoundaryLift CoefficientBassPositiveLeftPolynomialNodes
open CoefficientBassPositiveLeftPolynomialParameters
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- The first transported family is the original entire postcomposed polynomial simplex. -/
theorem first_simplex :
    ModelSimplex.ofIsos (polynomialReference P p q)
      (fun i ↦ (firstNodes P p q i).1) (fun i ↦ (firstNodes P p q i).2) =
    (CoefficientSquareFamilies.polynomialSimplex P p).postcomp
      (normalizedMap (coefficientMap P ((polynomialUnderFunctor R).map q))) := by
  have h : firstNodes P p q = fun i ↦ postReferenceNode (polynomialReference P p q)
      (normalizedMap (coefficientMap P ((polynomialUnderFunctor R).map q)))
      (firstAnchor P p q) (CoefficientSquareFamilies.polynomialNodes P p i) :=
    funext (first_nodes P p q)
  rw [h]
  unfold postReferenceNode
  rw [ModelSimplex.ofIsos_change_reference]
  exact (ModelSimplex.ofIsos_postcomp (CoefficientSquareFamilies.polynomialSource P p)
    (fun i ↦ (CoefficientSquareFamilies.polynomialNodes P p i).1)
    (fun i ↦ (CoefficientSquareFamilies.polynomialNodes P p i).2)
    (normalizedMap (coefficientMap P ((polynomialUnderFunctor R).map q)))).symm

/-- The second transported family is the original entire precomposed polynomial simplex. -/
theorem second_simplex :
    ModelSimplex.ofIsos (polynomialReference P p q)
      (fun i ↦ (secondNodes P p q i).1) (fun i ↦ (secondNodes P p q i).2) =
    (CoefficientSquareFamilies.polynomialSimplex P q).precomp
      (normalizedMap (coefficientMap P p)) := by
  have h : secondNodes P p q = fun i ↦ preReferenceNode (polynomialReference P p q)
      (normalizedMap (coefficientMap P p)) (secondAnchor P p q)
      (CoefficientSquareFamilies.polynomialNodes P q i) :=
    funext (second_nodes P p q)
  rw [h]
  unfold preReferenceNode
  rw [ModelSimplex.ofIsos_change_reference]
  exact (ModelSimplex.ofIsos_precomp (CoefficientSquareFamilies.polynomialSource P q)
    (fun i ↦ (CoefficientSquareFamilies.polynomialNodes P q i).1)
    (fun i ↦ (CoefficientSquareFamilies.polynomialNodes P q i).2)
    (normalizedMap (coefficientMap P p))).symm

/-- Every level and input has the exact original p-square value followed by polynomial q. -/
theorem first_family_native (n : ℕ) (t : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumFamily (polynomialReference P p q) (firstNodes P p q) n
      (NativeSquareFiveSimplex.parameter t, x) =
      (boundedFlatPerfectPrespectrumMap
        (coefficientMap P ((polynomialUnderFunctor R).map q))).map n
        ((boundedFlatCoefficientPolynomialSquareHomotopy P p).level n (t, x)) := by
  rw [prespectrumFamily_eq, first_simplex, prespectrumSimplexFamily_postcomp]
  exact congrArg
    ((boundedFlatPerfectPrespectrumMap
      (coefficientMap P ((polynomialUnderFunctor R).map q))).map n)
    (CoefficientSquareFamilies.polynomial_native P p n t x)

/-- Every level and input has the exact original q-square value after coefficient p. -/
theorem second_family_native (n : ℕ) (t : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumFamily (polynomialReference P p q) (secondNodes P p q) n
      (NativeSquareFiveSimplex.parameter t, x) =
      (boundedFlatCoefficientPolynomialSquareHomotopy P q).level n
        (t, (boundedFlatPerfectPrespectrumMap (coefficientMap P p)).map n x) := by
  rw [prespectrumFamily_eq, second_simplex, prespectrumSimplexFamily_precomp]
  exact CoefficientSquareFamilies.polynomial_native P q n t
    ((boundedFlatPerfectPrespectrumMap (coefficientMap P p)).map n x)

/-- The actual first polynomial-nerve path has that native value on its compact domain. -/
theorem first_parameter_native (n : ℕ) (t : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    pointwisePrespectrumFamily (polynomialReference P p q) n (firstParameter P p q t) x =
      (boundedFlatPerfectPrespectrumMap
        (coefficientMap P ((polynomialUnderFunctor R).map q))).map n
        ((boundedFlatCoefficientPolynomialSquareHomotopy P p).level n (t, x)) := by
  rw [pointwisePrespectrumFamily_eq_compact _ (firstParameter P p q)]
  exact (compactPrespectrumFamily_eq_simplex _ _ (firstNodes P p q) t
    (NativeSquareFiveSimplex.parameter t) rfl n x).trans (first_family_native P p q n t x)

/-- The actual second polynomial-nerve path has that native value on its compact domain. -/
theorem second_parameter_native (n : ℕ) (t : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    pointwisePrespectrumFamily (polynomialReference P p q) n (secondParameter P p q t) x =
      (boundedFlatCoefficientPolynomialSquareHomotopy P q).level n
        (t, (boundedFlatPerfectPrespectrumMap (coefficientMap P p)).map n x) := by
  rw [pointwisePrespectrumFamily_eq_compact _ (secondParameter P p q)]
  exact (compactPrespectrumFamily_eq_simplex _ _ (secondNodes P p q) t
    (NativeSquareFiveSimplex.parameter t) rfl n x).trans (second_family_native P p q n t x)

end Quillen.PerfectComplexes.CoefficientBassPositiveLeftPolynomialNative
