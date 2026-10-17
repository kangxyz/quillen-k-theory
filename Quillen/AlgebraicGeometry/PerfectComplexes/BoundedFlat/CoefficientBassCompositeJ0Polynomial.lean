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
namespace Quillen.PerfectComplexes.CoefficientBassCompositeJ0Polynomial
open CommonReferenceNerve CoefficientBassPositiveC1BoundaryLift
open CoefficientBassPositiveC0PolynomialEndpoints CoefficientBassPositiveC0CarrierAttachment
variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- The literal composite coefficient arrow, with its original normalized pullback. -/
abbrev arrow := p ≫ q

/-- The same polynomial reference used by the accepted actual C0 carrier. -/
abbrev reference := polynomialReference P p q

/-- The five original polynomial-square nodes before changing their reference. -/
abbrev originalNodes := NativeSquareFiveSimplex.nodes
  (coefficientMap P ((polynomialUnderFunctor R).map (arrow p q)))
  (polynomialProjection P a)
  (polynomialProjection P c)
  (coefficientMap P (arrow p q))
  (coefficientMap_naturality P (polynomialUnderCoefficient R) (arrow p q))

/-- Exact route from the chosen reference through the actual null input to square source. -/
def sourceAnchor : (reference P p q).functor ≅
    (NativeSquareFiveSimplex.source
      (coefficientMap P ((polynomialUnderFunctor R).map (arrow p q)))
      (polynomialProjection P a)).functor :=
  ((sourceNullNode P p q).2 ≪≫
    (BinaryNormalizationSimplex.total
      (polynomialProjection P c)
      (coefficientMap P (arrow p q))).symm) ≪≫
    (NativeSquareFiveSimplex.sourceIso
      (coefficientMap P ((polynomialUnderFunctor R).map (arrow p q)))
      (polynomialProjection P a)
      (polynomialProjection P c)
      (coefficientMap P (arrow p q))
      (coefficientMap_naturality P (polynomialUnderCoefficient R) (arrow p q))).symm

/-- All five dependent nodes retain the actual model maps and complete reference isomorphisms. -/
def nodes (i : Fin 5) : Node (reference P p q) :=
  ⟨(originalNodes P p q i).1, sourceAnchor P p q ≪≫ (originalNodes P p q i).2⟩

/-- Reference change preserves the full original simplex, not just either endpoint. -/
theorem simplex_original :
    ModelSimplex.ofIsos (reference P p q) (fun i ↦ (nodes P p q i).1)
      (fun i ↦ (nodes P p q i).2) =
    NativeSquareFiveSimplex.simplex
      (coefficientMap P ((polynomialUnderFunctor R).map (arrow p q)))
      (polynomialProjection P a)
      (polynomialProjection P c)
      (coefficientMap P (arrow p q))
      (coefficientMap_naturality P (polynomialUnderCoefficient R) (arrow p q)) :=
  ModelSimplex.ofIsos_change_reference (sourceAnchor P p q)
    (fun i ↦ (originalNodes P p q i).1) (fun i ↦ (originalNodes P p q i).2)

/-- Literal reversed-first, forward-second original clock, including all four primitive edges. -/
def movement : C(I, |nerve (Codiscrete (Node (reference P p q)))|) :=
  (parameter (reference P p q) (nodes P p q)).comp
    NativeSquareFiveSimplex.parameter.toContinuousMap

/-- The entire simplex path evaluates to the original polynomial square at every level. -/
theorem family_native (n : ℕ) (r : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))).space n) :
    prespectrumFamily (reference P p q) (nodes P p q) n
      (NativeSquareFiveSimplex.parameter r, x) =
      (boundedFlatCoefficientPolynomialSquareHomotopy P (arrow p q)).level n (r, x) := by
  rw [prespectrumFamily_eq, simplex_original]
  exact NativeSquareFiveSimplex.native _ _ _ _ _ n r x

/-- The full actual polynomial native lift needed by cone interchange is proved, not assumed. -/
theorem movement_native (n : ℕ) (r : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))).space n) :
    pointwisePrespectrumFamily (reference P p q) n (movement P p q r) x =
      (boundedFlatCoefficientPolynomialSquareHomotopy P (arrow p q)).level n (r, x) := by
  rw [pointwisePrespectrumFamily_eq_compact _ (movement P p q)]
  exact (compactPrespectrumFamily_eq_simplex _ _ (nodes P p q) r
    (NativeSquareFiveSimplex.parameter r) rfl n x).trans (family_native P p q n r x)

/-- The complete terminal polynomial node retains the source anchor of the given factorization. -/
theorem terminal_node : nodes P p q 4 = sourceNullNode P p q := by
  let ρ := (sourceNullNode P p q).2
  let β := BinaryNormalizationSimplex.total (polynomialProjection P c)
    (coefficientMap P (arrow p q))
  let α := NativeSquareFiveSimplex.sourceIso
    (coefficientMap P ((polynomialUnderFunctor R).map (arrow p q)))
    (polynomialProjection P a) (polynomialProjection P c) (coefficientMap P (arrow p q))
    (coefficientMap_naturality P (polynomialUnderCoefficient R) (arrow p q))
  change (⟨_, ((ρ ≪≫ β.symm) ≪≫ α.symm) ≪≫ (α ≪≫ β)⟩ : Node (reference P p q)) =
    ⟨_, ρ⟩
  exact congrArg (fun η ↦ (⟨(sourceNullNode P p q).1, η⟩ : Node (reference P p q)))
    (show ((ρ ≪≫ β.symm) ≪≫ α.symm) ≪≫ (α ≪≫ β) = ρ by simp [Iso.trans_assoc])

/-- The original coefficient-polynomial source node is retained in full. -/
theorem terminal_coefficient_node : nodes P p q 4 = coefficientPolynomialNodes P p q 0 :=
  (terminal_node P p q).trans (source_node P p q).symm

/-- The whole attached terminal node agrees with the raw positive rectangle. -/
theorem attached_terminal_node : ordinaryAttachNode P p q (nodes P p q 4) =
    BassH0Merge.nodes P p q (BassH0Diagram.plusFace.toOrderHom
      (DoubleSquareMergedSimplex.lastFace.toOrderHom (BassH0Merge.rightIndex 2))) := by
  rw [terminal_coefficient_node]
  exact (coefficient_column_nodes P p q 0).symm.trans
    (BassMOuterJoin.source_middle_plus_nodes P p q 2)

end Quillen.PerfectComplexes.CoefficientBassCompositeJ0Polynomial
