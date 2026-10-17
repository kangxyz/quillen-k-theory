/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassProjectionFourEdgeTargetSpanPolynomial
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNervePointwiseFamily

/-! All-level recovery of the original polynomial map and square on their complete input nerves. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassProjectionPath.WholeReference.FourEdge.TargetSpan
open BassH0Merge CommonReferenceNerve
variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (f : a ⟶ b)
variable {V : Model.{u + 1}}
  (E : V ⟶ modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))

/-- Every genuine polynomial input evaluates by the original polynomial coefficient map. -/
theorem polynomialMap_native (n : ℕ)
    (y : |nerve (Codiscrete (CommonReferenceNerve.Node
      (WholeReference.polynomialReference P a E)))|)
    (x : (prespectrum V).space n) :
    pointwisePrespectrumFamily (polynomialReference P f E) n (polynomialMap P f E y) x =
      (boundedFlatPerfectPrespectrumMap
        (coefficientMap P ((polynomialUnderFunctor R).map f))).map n
          (pointwisePrespectrumFamily (WholeReference.polynomialReference P a E) n y x) :=
  pointwisePrespectrumFamily_attachPostcomp (WholeReference.polynomialReference P a E)
    (polynomialPost P f) (polynomialReference P f E) (polynomialMapAnchor P f E) n y x

/-- The finite product square keeps the independent original coefficient and square parameters. -/
theorem polynomialSquare_finite_native {k : ℕ} (N : Fin (k + 1) → CommonReferenceNerve.Node E)
    (n : ℕ) (z : StdSimplex ℝ (Fin (k + 1))) (s : I) (x : (prespectrum V).space n) :
    prespectrumFamily (polynomialReference P f E)
      (FiniteParameter.gridNodes E (polynomialReference P f E)
        (polynomialSquareNodes P f E) N) n
      (SimplexGrid.parameter.{u + 1} k 4 (z, NativeSquareFiveSimplex.parameter s), x) =
    (boundedFlatCoefficientPolynomialSquareHomotopy P f).level n
      (s, prespectrumFamily E N n (z, x)) := by
  rw [prespectrumFamily_eq, prespectrumFamily_eq]
  have hs : ModelSimplex.ofIsos (polynomialReference P f E)
      (fun i ↦ (FiniteParameter.gridNodes E (polynomialReference P f E)
        (polynomialSquareNodes P f E) N i).1)
      (fun i ↦ (FiniteParameter.gridNodes E (polynomialReference P f E)
        (polynomialSquareNodes P f E) N i).2) =
      CommonReferenceProduct.simplex E (fun i ↦ (N i).1) (fun i ↦ (N i).2)
        (CoefficientSquareFamilies.polynomialSource P f)
        (fun i ↦ (CoefficientSquareFamilies.polynomialNodes P f i).1)
        (fun i ↦ (CoefficientSquareFamilies.polynomialNodes P f i).2) :=
    ModelSimplex.ofIsos_change_reference (polynomialSquareAnchor P f E) _ _
  rw [hs, CommonReferenceProduct.prespectrum_comp]
  exact CoefficientSquareFamilies.polynomial_native P f n s _

/-- All native levels, including actual degree-zero loops, retain the unchanged square clock. -/
theorem polynomialSquare_native (n : ℕ)
    (y : |nerve (Codiscrete (CommonReferenceNerve.Node E))|) (s : I)
    (x : (prespectrum V).space n) :
    pointwisePrespectrumFamily (polynomialReference P f E) n
      (polynomialSquare P f E (y, s)) x =
    (boundedFlatCoefficientPolynomialSquareHomotopy P f).level n
      (s, pointwisePrespectrumFamily E n y x) := by
  obtain ⟨k, N, z, hz⟩ := exists_parameter E y
  rw [← hz, polynomialSquare_characteristic, pointwisePrespectrumFamily_parameter,
    pointwisePrespectrumFamily_parameter]
  exact polynomialSquare_finite_native P f E N n z s x

end Quillen.PerfectComplexes.BassProjectionPath.WholeReference.FourEdge.TargetSpan
