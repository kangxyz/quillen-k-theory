/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveC1PolynomialSourceReference
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassCompositeJ0Polynomial

/-! Full polynomial source references for the original composite-arrow C1 entrance. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters
open scoped Simplicial Topology unitInterval
universe u v
namespace Quillen.PerfectComplexes.CoefficientBassCompositeC1PolynomialSourceReference
open BassH0Merge CommonReferenceNerve CoefficientBassPositiveC1BoundaryLift
open CoefficientBassPositiveC1PolynomialSourceReference
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- The source model functor retains the exact polynomial-composite equality. -/
theorem initial_functor : (polynomialReference P p q).functor =
    (CoefficientBassCompositeJ0Polynomial.nodes P p q 2).1.functor :=
  congrArg (fun f ↦ (normalizedMap (polynomialProjection P a) ≫ normalizedMap f).functor)
    (polynomial_composite P p q).symm

/-- The entire original square-reference loop is precisely its source-factor transport. -/
theorem initial_reference :
    (CoefficientBassCompositeJ0Polynomial.nodes P p q 2).2 =
      eqToIso (initial_functor P p q) := by
  have h := NativeSquareReferenceCancellation.source_reference
    (coefficientMap P ((polynomialUnderFunctor R).map q) ≫
      coefficientMap P ((polynomialUnderFunctor R).map p))
    (coefficientMap P ((polynomialUnderFunctor R).map (p ≫ q)))
    (polynomialProjection P a) (polynomialProjection P c)
    (coefficientMap P q ≫ coefficientMap P p) (coefficientMap P (p ≫ q))
    (polynomial_composite P p q).symm (coefficientMap_comp P p q).symm
    (outer_square P p q)
    (coefficientMap_naturality P (polynomialUnderCoefficient R) (p ≫ q))
  rw [← moving_side_reference] at h
  simp only [← Iso.trans_assoc] at h
  change (CoefficientBassCompositeJ0Polynomial.nodes P p q 2).2 =
    eqToIso (initial_functor P p q) at h
  exact h

private theorem reflexive_node_eq {V W : Model.{v}} {F : V ⟶ W}
    (N : Node F) (h : F.functor = N.1.functor) (he : N.2 = eqToIso h) :
    (⟨F, Iso.refl F.functor⟩ : Node F) = N := by
  rcases N with ⟨G, ρ⟩
  change ρ = eqToIso h at he
  apply ModelSimplex.reference_node_eq h
  simpa only [Iso.refl_hom, Category.id_comp, eqToIso.hom] using
    (congrArg Iso.hom he).symm

private theorem precomp_reflexive {V W T : Model.{v}} (J : T ⟶ V) (F : V ⟶ W) :
    precompNode J (⟨F, Iso.refl F.functor⟩ : Node F) =
      (⟨J ≫ F, Iso.refl (J ≫ F).functor⟩ : Node (J ≫ F)) := by
  change (⟨J ≫ F, isoWhiskerLeft J.functor (Iso.refl F.functor)⟩ : Node (J ≫ F)) = _
  rw [isoWhiskerLeft_refl]
  rfl

/-- Equality of complete polynomial nodes, proved before the Laurent attachment. -/
theorem polynomial_source_node : polynomialNodes P p q 0 =
    CoefficientBassCompositeJ0Polynomial.nodes P p q 2 := by
  change precompNode (BassOverlap.projectionMap P (a := a))
    (⟨BassMOuterJoin.sideBinarySource P p q, Iso.refl _⟩ :
      Node (BassMOuterJoin.sideBinarySource P p q)) = _
  rw [precomp_reflexive]
  exact reflexive_node_eq (CoefficientBassCompositeJ0Polynomial.nodes P p q 2)
    (initial_functor P p q) (initial_reference P p q)

private theorem parameter_vertex {V W : Model.{v}} (F : V ⟶ W) {k : ℕ}
    (N : Fin (k + 1) → Node F) (i : Fin (k + 1)) :
    parameter F N (StdSimplex.single i) =
      CoefficientBassPositiveC0PolynomialEndpoints.nodePoint F (N i) := by
  let α : ⦋0⦌ ⟶ ⦋k⦌ := SimplexCategory.Hom.mk ⟨fun _ ↦ i, fun _ _ _ ↦ le_refl i⟩
  have hm : StdSimplex.map α.toOrderHom
      (StdSimplex.single (0 : Fin 1) : StdSimplex ℝ (Fin 1)) =
      StdSimplex.single i := by
    rw [StdSimplex.map_single]
    rfl
  rw [← hm, parameter_face]
  rfl

/-- The whole polynomial source point is the original old-cone input. -/
theorem polynomial_zero : polynomialParameter P p q 0 =
    CoefficientBassCompositeJ0Polynomial.movement P p q 0 := by
  change parameter _ _ (pausedBinaryParameter 0) =
    parameter _ _ (NativeSquareFiveSimplex.parameter 0)
  rw [Path.source, Path.source, parameter_vertex, parameter_vertex, polynomial_source_node]

end Quillen.PerfectComplexes.CoefficientBassCompositeC1PolynomialSourceReference
