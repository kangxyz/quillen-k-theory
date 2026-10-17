/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import
Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveC0PolynomialEndpoints
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.NativeSquareFiveSimplex

/-!
# Original polynomial movement in the chosen actual C0 reference

The five-node polynomial square, rather than the coefficient-composition triangle, gives
this entire moving path. Its reference is anchored through the accepted actual direct-l
null input. Both original normalization intermediates, source equality and path clock are
retained. The further full-reference equality with the raw positive chart row is separate.
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
namespace Quillen.PerfectComplexes.CoefficientBassPositiveJ0PolynomialMovement
open CommonReferenceNerve CoefficientBassPositiveC1BoundaryLift
open CoefficientBassPositiveC0PolynomialEndpoints
variable {R : CommRingCat.{u}} (P : Over (Spec R)) (d : Under R)

/-- Exactly the original Laurent coefficient arrow, without replacing it by a composite. -/
abbrev arrow := (laurentUnderCoefficient R).app d

/-- The same polynomial reference used by the accepted actual C0 carrier. -/
abbrev reference := polynomialReference P ((polynomialUnderCoefficient R).app d)
  ((underToLaurent R).app d)

/-- The five original polynomial-square nodes before changing their reference. -/
abbrev originalNodes := NativeSquareFiveSimplex.nodes
  (coefficientMap P ((polynomialUnderFunctor R).map (arrow d)))
  (polynomialProjection P d)
  (polynomialProjection P ((laurentUnderFunctor R).obj d))
  (coefficientMap P (arrow d))
  (coefficientMap_naturality P (polynomialUnderCoefficient R) (arrow d))

/-- Exact route from the chosen reference through the actual null input to square source. -/
def sourceAnchor : (reference P d).functor ≅
    (NativeSquareFiveSimplex.source
      (coefficientMap P ((polynomialUnderFunctor R).map (arrow d)))
      (polynomialProjection P d)).functor :=
  ((actualSourceNullNode P d).2 ≪≫
    (BinaryNormalizationSimplex.total
      (polynomialProjection P ((laurentUnderFunctor R).obj d))
      (coefficientMap P (arrow d))).symm) ≪≫
    (NativeSquareFiveSimplex.sourceIso
      (coefficientMap P ((polynomialUnderFunctor R).map (arrow d)))
      (polynomialProjection P d)
      (polynomialProjection P ((laurentUnderFunctor R).obj d))
      (coefficientMap P (arrow d))
      (coefficientMap_naturality P (polynomialUnderCoefficient R) (arrow d))).symm

/-- All five dependent nodes retain the actual model maps and complete reference isomorphisms. -/
def nodes (i : Fin 5) : Node (reference P d) :=
  ⟨(originalNodes P d i).1, sourceAnchor P d ≪≫ (originalNodes P d i).2⟩

/-- Reference change preserves the full original simplex, not just either endpoint. -/
theorem simplex_original :
    ModelSimplex.ofIsos (reference P d) (fun i ↦ (nodes P d i).1)
      (fun i ↦ (nodes P d i).2) =
    NativeSquareFiveSimplex.simplex
      (coefficientMap P ((polynomialUnderFunctor R).map (arrow d)))
      (polynomialProjection P d)
      (polynomialProjection P ((laurentUnderFunctor R).obj d))
      (coefficientMap P (arrow d))
      (coefficientMap_naturality P (polynomialUnderCoefficient R) (arrow d)) :=
  ModelSimplex.ofIsos_change_reference (sourceAnchor P d)
    (fun i ↦ (originalNodes P d i).1) (fun i ↦ (originalNodes P d i).2)

/-- Literal reversed-first, forward-second original clock, including all four primitive edges. -/
def movement : C(I, |nerve (Codiscrete (Node (reference P d)))|) :=
  (parameter (reference P d) (nodes P d)).comp
    NativeSquareFiveSimplex.parameter.toContinuousMap

/-- The entire simplex path evaluates to the original polynomial square at every level. -/
theorem family_native (n : ℕ) (r : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, d))))).space n) :
    prespectrumFamily (reference P d) (nodes P d) n
      (NativeSquareFiveSimplex.parameter r, x) =
      (boundedFlatCoefficientPolynomialSquareHomotopy P (arrow d)).level n (r, x) := by
  rw [prespectrumFamily_eq, simplex_original]
  exact NativeSquareFiveSimplex.native _ _ _ _ _ n r x

/-- The full actual polynomial native lift needed by cone interchange is proved, not assumed. -/
theorem movement_native (n : ℕ) (r : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, d))))).space n) :
    pointwisePrespectrumFamily (reference P d) n (movement P d r) x =
      (boundedFlatCoefficientPolynomialSquareHomotopy P (arrow d)).level n (r, x) := by
  rw [pointwisePrespectrumFamily_eq_compact _ (movement P d)]
  exact (compactPrespectrumFamily_eq_simplex _ _ (nodes P d) r
    (NativeSquareFiveSimplex.parameter r) rfl n x).trans (family_native P d n r x)

end Quillen.PerfectComplexes.CoefficientBassPositiveJ0PolynomialMovement
