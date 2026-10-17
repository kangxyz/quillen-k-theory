/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveC0CarrierRails

/-!
# Full polynomial null-input endpoints of the original C0 rail

The original coefficient triangle is transported in the polynomial reference itself. Its
source is the direct-composite polynomial null input; its target is the original q null
input precomposed by p. Equality-induced source transports and the full normalization
reference are retained. The two cone tips are untouched.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters Quillen.NativePathCells
open scoped Simplicial Topology unitInterval
universe u v
namespace Quillen.PerfectComplexes.CoefficientBassPositiveC0PolynomialEndpoints
open BassH0Merge CommonReferenceNerve CoefficientBassPositiveC1BoundaryLift
open CoefficientBassPositiveC0CarrierAttachment CoefficientBassPositiveC0CarrierRails

private theorem change_full_node {V W : Model.{v}} (F G H : V ⟶ W)
    (h : G.functor = H.functor) (ρ : F.functor ≅ G.functor) :
    (⟨G, ρ⟩ : Node F) = ⟨H, ρ ≪≫ eqToIso h⟩ := by
  apply ModelSimplex.reference_node_eq h
  rfl

private theorem attach_source_change {V W X : Model.{v}}
    (F : V ⟶ W) (J : W ⟶ X) (K H : V ⟶ X)
    (ρ : K.functor ≅ (F ≫ J).functor) (h : (F ≫ J).functor = H.functor) :
    attachPostcompNode F J K ρ (⟨F, Iso.refl _⟩ : Node F) =
      (⟨H, ρ ≪≫ eqToIso h⟩ : Node K) := by
  unfold attachPostcompNode
  change (⟨F ≫ J, ρ ≪≫ isoWhiskerRight (Iso.refl _) J.functor⟩ : Node K) = _
  have hρ : ρ ≪≫ isoWhiskerRight (Iso.refl F.functor) J.functor = ρ := by
    have hi : isoWhiskerRight (Iso.refl F.functor) J.functor =
        Iso.refl (F ≫ J).functor := by
      rw [isoWhiskerRight_refl]
      rfl
    exact (congrArg (fun ε ↦ ρ ≪≫ ε) hi).trans (Iso.trans_refl ρ)
  exact (congrArg (fun ε : K.functor ≅ (F ≫ J).functor ↦
    (⟨F ≫ J, ε⟩ : Node K)) hρ).trans (change_full_node K (F ≫ J) H h ρ)

/-- Characteristic vertex of a full reference node; no native evaluator is used. -/
def nodePoint {V W : Model.{v}} (F : V ⟶ W) (N : Node F) :
    |nerve (Codiscrete (Node F))| := parameter F (fun _ : Fin 1 ↦ N) (StdSimplex.single 0)

private theorem parameter_vertex {V W : Model.{v}} (F : V ⟶ W) {k : ℕ}
    (N : Fin (k + 1) → Node F) (i : Fin (k + 1)) :
    parameter F N (StdSimplex.single i) = nodePoint F (N i) := by
  let α : ⦋0⦌ ⟶ ⦋k⦌ := SimplexCategory.Hom.mk ⟨fun _ ↦ i, fun _ _ _ ↦ le_refl i⟩
  have hm : StdSimplex.map α.toOrderHom
      (StdSimplex.single (0 : Fin 1) : StdSimplex ℝ (Fin 1)) =
      StdSimplex.single i := by
    rw [StdSimplex.map_single]
    rfl
  rw [← hm, parameter_face]
  rfl

variable {R : CommRingCat.{u}} (P : Over (Spec R))

/-- Exact model input to the polynomial half of the original positive null after w. -/
def polynomialNullInput {d e : Under R} (w : d ⟶ e) :=
  normalizedMap (coefficientMap P w) ≫ normalizedMap (polynomialProjection P e)

variable {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- The original coefficient-composition source equality before applying any Laurent chart. -/
theorem sourceInputEq :
    (BassMComponents.coefficientSource P p q ≫ normalizedMap (polynomialProjection P c)).functor =
      (polynomialNullInput P (p ≫ q)).functor :=
  congrArg (fun f ↦ (normalizedMap f ≫ normalizedMap (polynomialProjection P c)).functor)
    (coefficientMap_comp P p q).symm

/-- Exact association of the original normalized target factors, at the polynomial model level. -/
theorem targetInputEq :
    (BinaryNormalizationSimplex.targetMap (coefficientMap P q) (coefficientMap P p) ≫
      normalizedMap (polynomialProjection P c)).functor =
    (normalizedMap (coefficientMap P p) ≫ polynomialNullInput P q).functor := rfl

/-- Original source anchor, retaining the explicit coefficient-map composite equality. -/
def sourceNullAnchor : (polynomialReference P p q).functor ≅
    (polynomialNullInput P (p ≫ q)).functor :=
  polynomialCoefficientAnchor P p q ≪≫ eqToIso (sourceInputEq P p q)

/-- Original target anchor, including the whole coefficient normalization and exact association. -/
def targetNullAnchor : (polynomialReference P p q).functor ≅
    (normalizedMap (coefficientMap P p) ≫ polynomialNullInput P q).functor :=
  (polynomialCoefficientAnchor P p q ≪≫ isoWhiskerRight
    (BinaryNormalizationSimplex.total (coefficientMap P q) (coefficientMap P p))
    (normalizedMap (polynomialProjection P c)).functor) ≪≫ eqToIso (targetInputEq P p q)

/-- Direct-composite polynomial null input with its entire original source reference. -/
def sourceNullNode : Node (polynomialReference P p q) :=
  ⟨polynomialNullInput P (p ≫ q), sourceNullAnchor P p q⟩

/-- The original q polynomial null input, precomposed by precisely the original p. -/
def targetNullNode : Node (polynomialReference P p q) :=
  preReferenceNode (polynomialReference P p q) (normalizedMap (coefficientMap P p))
    (targetNullAnchor P p q) (⟨polynomialNullInput P q, Iso.refl _⟩ :
    Node (polynomialNullInput P q))

/-- Full source node equality proved in the polynomial reference, not by Laurent cancellation. -/
theorem source_node : coefficientPolynomialNodes P p q 0 = sourceNullNode P p q := by
  rw [coefficientPolynomial_nodes]
  exact attach_source_change.{u + 1}
    (BassMComponents.coefficientSource P p q) (normalizedMap (polynomialProjection P c))
    (polynomialReference P p q) (polynomialNullInput P (p ≫ q))
    (polynomialCoefficientAnchor P p q) (sourceInputEq P p q)

/-- Full target node equality retains the normalization iso before the q-pre-p null input. -/
theorem target_node : coefficientPolynomialNodes P p q 2 = targetNullNode P p q := by
  rw [coefficientPolynomial_nodes]
  unfold targetNullNode
  rw [preReferenceNode_source]
  exact change_full_node _ _ _ (targetInputEq P p q)
    (polynomialCoefficientAnchor P p q ≪≫ isoWhiskerRight
      (BinaryNormalizationSimplex.total (coefficientMap P q) (coefficientMap P p))
      (normalizedMap (polynomialProjection P c)).functor)

/-- Source endpoint of the entire polynomial binary parameter at its unchanged time zero. -/
theorem source_parameter : coefficientPolynomialParameter P p q 0 =
    nodePoint (polynomialReference P p q) (sourceNullNode P p q) := by
  change parameter _ _ (binaryPath (k := 2) 0 1 2 0) = _
  rw [Path.source, parameter_vertex, source_node]

/-- Target endpoint of that parameter, retaining the whole q-pre-p reference node. -/
theorem target_parameter : coefficientPolynomialParameter P p q 1 =
    nodePoint (polynomialReference P p q) (targetNullNode P p q) := by
  change parameter _ _ (binaryPath (k := 2) 0 1 2 1) = _
  rw [Path.target, parameter_vertex, target_node]

/-- The actual p;q=l source transport on the polynomial null input, stated explicitly. -/
theorem actualSourceInputEq (d : Under R) :
    (BassMComponents.coefficientSource P ((polynomialUnderCoefficient R).app d)
      ((underToLaurent R).app d) ≫
      normalizedMap (polynomialProjection P ((laurentUnderFunctor R).obj d))).functor =
    (polynomialNullInput P ((laurentUnderCoefficient R).app d)).functor :=
  (sourceInputEq P ((polynomialUnderCoefficient R).app d) ((underToLaurent R).app d)).trans
    (congrArg (fun w ↦ (polynomialNullInput P w).functor)
      (polynomialUnderCoefficient_toLaurent R d))

/-- Full actual direct-l null node, including the original p;q=l equality-induced reference. -/
def actualSourceNullNode (d : Under R) :
    Node (polynomialReference P ((polynomialUnderCoefficient R).app d)
    ((underToLaurent R).app d)) :=
  ⟨polynomialNullInput P ((laurentUnderCoefficient R).app d),
    polynomialCoefficientAnchor P ((polynomialUnderCoefficient R).app d)
      ((underToLaurent R).app d) ≪≫ eqToIso (actualSourceInputEq P d)⟩

/-- The actual source full node, with no silent substitution of l for the composite. -/
theorem actual_source_node (d : Under R) :
    coefficientPolynomialNodes P ((polynomialUnderCoefficient R).app d)
      ((underToLaurent R).app d) 0 = actualSourceNullNode P d := by
  rw [coefficientPolynomial_nodes]
  exact attach_source_change.{u + 1}
    (BassMComponents.coefficientSource P ((polynomialUnderCoefficient R).app d)
      ((underToLaurent R).app d))
    (normalizedMap (polynomialProjection P ((laurentUnderFunctor R).obj d)))
    (polynomialReference P ((polynomialUnderCoefficient R).app d) ((underToLaurent R).app d))
    (polynomialNullInput P ((laurentUnderCoefficient R).app d))
    (polynomialCoefficientAnchor P ((polynomialUnderCoefficient R).app d)
      ((underToLaurent R).app d)) (actualSourceInputEq P d)

/-- Whole actual direct-l polynomial endpoint in the fixed polynomial carrier. -/
theorem actual_source_parameter (d : Under R) :
    coefficientPolynomialParameter P ((polynomialUnderCoefficient R).app d)
      ((underToLaurent R).app d) 0 =
    nodePoint _ (actualSourceNullNode P d) := by
  change parameter _ _ (binaryPath (k := 2) 0 1 2 0) = _
  rw [Path.source, parameter_vertex, actual_source_node]

/-- Both distinct-tip cylinder rails retain the complete source polynomial null input. -/
theorem source_cylinders (t : I) :
    CutOpenCarrier.cylinderMinus (polynomialReference P p q) (chartMap P (c := c))
        (laurentReference P p q) (ordinaryAnchor P p q)
        (LaurentUnitReferenceSpecialization.shiftedAnchor P p q)
      (coefficientPolynomialParameter P p q 0, t) =
    CutOpenCarrier.cylinderMinus (polynomialReference P p q) (chartMap P (c := c))
        (laurentReference P p q) (ordinaryAnchor P p q)
        (LaurentUnitReferenceSpecialization.shiftedAnchor P p q)
      (nodePoint _ (sourceNullNode P p q), t) ∧
    CutOpenCarrier.cylinderPlus (polynomialReference P p q) (chartMap P (c := c))
        (laurentReference P p q) (ordinaryAnchor P p q)
        (LaurentUnitReferenceSpecialization.shiftedAnchor P p q)
      (coefficientPolynomialParameter P p q 0, t) =
    CutOpenCarrier.cylinderPlus (polynomialReference P p q) (chartMap P (c := c))
        (laurentReference P p q) (ordinaryAnchor P p q)
        (LaurentUnitReferenceSpecialization.shiftedAnchor P p q)
      (nodePoint _ (sourceNullNode P p q), t) := by
  rw [source_parameter]
  exact ⟨rfl, rfl⟩

/-- Both distinct-tip cylinder rails retain the complete target polynomial null input. -/
theorem target_cylinders (t : I) :
    CutOpenCarrier.cylinderMinus (polynomialReference P p q) (chartMap P (c := c))
        (laurentReference P p q) (ordinaryAnchor P p q)
        (LaurentUnitReferenceSpecialization.shiftedAnchor P p q)
      (coefficientPolynomialParameter P p q 1, t) =
    CutOpenCarrier.cylinderMinus (polynomialReference P p q) (chartMap P (c := c))
        (laurentReference P p q) (ordinaryAnchor P p q)
        (LaurentUnitReferenceSpecialization.shiftedAnchor P p q)
      (nodePoint _ (targetNullNode P p q), t) ∧
    CutOpenCarrier.cylinderPlus (polynomialReference P p q) (chartMap P (c := c))
        (laurentReference P p q) (ordinaryAnchor P p q)
        (LaurentUnitReferenceSpecialization.shiftedAnchor P p q)
      (coefficientPolynomialParameter P p q 1, t) =
    CutOpenCarrier.cylinderPlus (polynomialReference P p q) (chartMap P (c := c))
        (laurentReference P p q) (ordinaryAnchor P p q)
        (LaurentUnitReferenceSpecialization.shiftedAnchor P p q)
      (nodePoint _ (targetNullNode P p q), t) := by
  rw [target_parameter]
  exact ⟨rfl, rfl⟩

end Quillen.PerfectComplexes.CoefficientBassPositiveC0PolynomialEndpoints
