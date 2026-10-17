/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassCompositeJ0Polynomial
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassNegativeSeedReferenceRails

/-! The original polynomial movement has a full composite-only reference normal form. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassCompositeJ0PolynomialTransport
open CommonReferenceNerve CoefficientBassNegativeCarrierReference
open CoefficientBassNegativeSeedReferenceRails
variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a c : Under R}

/-- The original square's five full nodes depend on the literal composite arrow. -/
abbrev originalNodes (k : a ⟶ c) := NativeSquareFiveSimplex.nodes
  (coefficientMap P ((polynomialUnderFunctor R).map k))
  (polynomialProjection P a) (polynomialProjection P c) (coefficientMap P k)
  (coefficientMap_naturality P (polynomialUnderCoefficient R) k)

/-- The exact old source anchor, expressed through the already-proved full source-null node. -/
def sourceAnchor (D : SeedGeometry P (a := a) (c := c)) :
    (Geometry.polyRef P D.carrier).functor ≅
      (NativeSquareFiveSimplex.source
        (coefficientMap P ((polynomialUnderFunctor R).map D.arrow))
        (polynomialProjection P a)).functor :=
  ((SeedGeometry.polynomialNode P D).2 ≪≫
    (BinaryNormalizationSimplex.total (polynomialProjection P c)
      (coefficientMap P D.arrow)).symm) ≪≫
    (NativeSquareFiveSimplex.sourceIso
      (coefficientMap P ((polynomialUnderFunctor R).map D.arrow))
      (polynomialProjection P a) (polynomialProjection P c) (coefficientMap P D.arrow)
      (coefficientMap_naturality P (polynomialUnderCoefficient R) D.arrow)).symm

/-- Each node retains its entire original model map and complete source anchor. -/
def nodes (D : SeedGeometry P (a := a) (c := c)) (i : Fin 5) :
    Node (Geometry.polyRef P D.carrier) :=
  ⟨(originalNodes P D.arrow i).1, sourceAnchor P D ≪≫ (originalNodes P D.arrow i).2⟩

/-- The fixed original five-node clock is unchanged by the normal form. -/
def movement (D : SeedGeometry P (a := a) (c := c)) :
    C(I, |nerve (Codiscrete (Node (Geometry.polyRef P D.carrier)))|) :=
  (parameter (Geometry.polyRef P D.carrier) (nodes P D)).comp
    NativeSquareFiveSimplex.parameter.toContinuousMap

variable {b b' : Under R} (p : a ⟶ b) (q : b ⟶ c) (p' : a ⟶ b') (q' : b' ⟶ c)

/-- The actual source anchor is exactly the existing full-node normal form. -/
theorem sourceAnchor_normal : CoefficientBassCompositeJ0Polynomial.sourceAnchor P p q =
    sourceAnchor P (seedGeometry P p q) := by
  have hs := eq_of_heq (Sigma.mk.inj (c0_source_node_normal P p q)).2
  exact congrArg (fun ρ ↦
    (ρ ≪≫ (BinaryNormalizationSimplex.total (polynomialProjection P c)
      (coefficientMap P (p ≫ q))).symm) ≪≫
      (NativeSquareFiveSimplex.sourceIso
        (coefficientMap P ((polynomialUnderFunctor R).map (p ≫ q)))
        (polynomialProjection P a) (polynomialProjection P c) (coefficientMap P (p ≫ q))
        (coefficientMap_naturality P (polynomialUnderCoefficient R) (p ≫ q))).symm) hs

/-- All five actual nodes, including their anchors, have the same explicit normal form. -/
theorem nodes_normal : CoefficientBassCompositeJ0Polynomial.nodes P p q =
    nodes P (seedGeometry P p q) := by
  funext i
  unfold CoefficientBassCompositeJ0Polynomial.nodes nodes
  rw [sourceAnchor_normal]
  rfl

/-- The entire original polynomial path, including its two clocks, is retained. -/
theorem movement_normal : CoefficientBassCompositeJ0Polynomial.movement P p q =
    movement P (seedGeometry P p q) := by
  unfold CoefficientBassCompositeJ0Polynomial.movement movement
  rw [nodes_normal]
  rfl

/-- Equal complete seed geometry transports the entire parameter value dependently. -/
theorem movement_geometry_heq {D E : SeedGeometry P (a := a) (c := c)}
    (h : D = E) (r : I) : HEq (movement P D r) (movement P E r) := by
  subst E
  rfl

/-- Two actual factorizations of the same arrow preserve the whole polynomial movement. -/
theorem movement_heq (h : p ≫ q = p' ≫ q') (r : I) :
    HEq (CoefficientBassCompositeJ0Polynomial.movement P p q r)
      (CoefficientBassCompositeJ0Polynomial.movement P p' q' r) := by
  rw [movement_normal, movement_normal]
  exact movement_geometry_heq P (seed_geometry_eq P p q p' q' h) r

end Quillen.PerfectComplexes.CoefficientBassCompositeJ0PolynomialTransport
