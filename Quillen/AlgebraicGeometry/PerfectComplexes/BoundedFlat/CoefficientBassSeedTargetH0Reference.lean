/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSeedTargetReferenceTransport
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassH0Diagram
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceReanchorAttachment

/-! Exact normalization between the original H0 target reference and the added sheet reference. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.CoefficientBassSeedTargetH0Reference
open BassH0Merge CommonReferenceNerve CommonReferenceProduct
open CoefficientBassSeedTargetChartAttachment CoefficientBassSeedTargetReferenceTransport
variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (f : a ⟶ b)

/-- The source Bass projection retains the explicit positive-chart projection equality. -/
def projectionReferenceIso :
    (normalizedMap (laurentProjection P a)).functor ≅ (BassProjectionPath.source P a).functor :=
  eqToIso (congrArg (fun g ↦ (normalizedMap g).functor) (laurentPlus_projection P a).symm)

/-- The original H0 binary total, followed by the explicit source-projection transport. -/
def h0ProjectionIso : (BassH0Diagram.reference P f).functor ≅
    (BassProjectionPath.source P a ≫ L P f).functor :=
  BinaryNormalizationSimplex.total
    (coefficientMap P ((laurentUnderFunctor R).map f)) (laurentProjection P a) ≪≫
      isoWhiskerRight (projectionReferenceIso P (a := a)) (L P f).functor

variable {V : Model.{u + 1}}
  (E : V ⟶ modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))
  (G : V ⟶ modelOf (boundedFlatPerfectWaldhausen
    (space (op P, (laurentUnderFunctor R).obj a))))
  (τ : (BassProjectionPath.WholeReference.reference P a E).functor ≅ G.functor)

/-- The full H0 reference maps to the unchanged postcomposed original Laurent reference. -/
def referenceBridge : (E ≫ BassH0Diagram.reference P f).functor ≅ (G ≫ L P f).functor :=
  isoWhiskerLeft E.functor (h0ProjectionIso P f) ≪≫
    (Functor.associator E.functor (BassProjectionPath.source P a).functor
      (L P f).functor).symm ≪≫ isoWhiskerRight τ (L P f).functor

/-- Compare the two actual target references through their common postcomposed source reference. -/
def targetReferenceIso :
    (BassProjectionPath.WholeReference.reference P b (targetInput P f E)).functor ≅
      (E ≫ BassH0Diagram.reference P f).functor :=
  referenceIso P f E G τ ≪≫ (referenceBridge P f E G τ).symm

/-- The reference triangle commutes as a full isomorphism, with every normalization retained. -/
theorem reference_triangle :
    targetReferenceIso P f E G τ ≪≫ referenceBridge P f E G τ = referenceIso P f E G τ := by
  simp only [targetReferenceIso, Iso.trans_assoc, Iso.symm_self_id, Iso.trans_refl]

/-- Every dependent Laurent node has the identical full reference through either target route. -/
theorem target_node (N : Node (G ≫ L P f)) :
    reanchor (targetReferenceIso P f E G τ) (reanchor (referenceBridge P f E G τ) N) =
      reanchor (referenceIso P f E G τ) N := by
  rcases N with ⟨K, ρ⟩
  change (⟨K, targetReferenceIso P f E G τ ≪≫ (referenceBridge P f E G τ ≪≫ ρ)⟩ :
    Node (BassProjectionPath.WholeReference.reference P b (targetInput P f E))) =
    ⟨K, referenceIso P f E G τ ≪≫ ρ⟩
  apply congrArg (fun η ↦ (⟨K, η⟩ :
    Node (BassProjectionPath.WholeReference.reference P b (targetInput P f E))))
  rw [← Iso.trans_assoc, reference_triangle]

end Quillen.PerfectComplexes.CoefficientBassSeedTargetH0Reference
