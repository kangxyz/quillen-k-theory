/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSeedTerminalTargetTriangle

/-! The original terminal seed sheets retain both complete reference transports. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.CoefficientBassSeedTerminalAttachmentTriangle

private theorem paste {C : Type u} [Category C] {A0 A1 A2 A3 B0 B1 B2 B3 : C}
    (ta : A0 ≅ A1) (a : A1 ≅ B1) (b : A0 ≅ B0) (s : B0 ≅ B1)
    (d : B0 ≅ B2) (z : B2 ≅ B3) (k : A0 ≅ A2) (t : A2 ≅ B2)
    (u : A2 ≅ A3) (v : A3 ≅ B3)
    (hs : ta ≪≫ a = b ≪≫ s) (hi : b ≪≫ d = k ≪≫ t) (ht : t ≪≫ z = u ≪≫ v) :
    a ≪≫ (s.symm ≪≫ d ≪≫ z) = (ta.symm ≪≫ k ≪≫ u) ≪≫ v := by
  calc
    a ≪≫ (s.symm ≪≫ d ≪≫ z) =
        ta.symm ≪≫ (ta ≪≫ a) ≪≫ s.symm ≪≫ d ≪≫ z := by
      simp only [Iso.trans_assoc, Iso.symm_self_id_assoc]
    _ = ta.symm ≪≫ (b ≪≫ s) ≪≫ s.symm ≪≫ d ≪≫ z := by rw [hs]
    _ = ta.symm ≪≫ (b ≪≫ d) ≪≫ z := by
      simp only [Iso.trans_assoc, Iso.self_symm_id_assoc]
    _ = ta.symm ≪≫ (k ≪≫ t) ≪≫ z := by rw [hi]
    _ = (ta.symm ≪≫ k ≪≫ u) ≪≫ v := by
      simpa only [Iso.trans_assoc] using congrArg (fun x ↦ ta.symm ≪≫ k ≪≫ x) ht

open BassH0Merge BassMWholeNerve CoefficientBassSeedCarrierLaurentReference
open CoefficientBassPositiveC1BoundaryLift CoefficientBassSeedTargetChartAttachment
open CoefficientBassSeedTerminalInputTriangle
variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (f : a ⟶ b)
  (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
local notation "pa" => CategoryTheory.NatTrans.app (polynomialUnderCoefficient R) a
local notation "qa" => CategoryTheory.NatTrans.app α a
local notation "pb" => CategoryTheory.NatTrans.app (polynomialUnderCoefficient R) b
local notation "qb" => CategoryTheory.NatTrans.app α b
local notation "lf" => CategoryTheory.Functor.map (laurentUnderFunctor R) f
local notation "U" => coefficientModel P f
local notation "K" => Jb P (b := CategoryTheory.Functor.obj (laurentUnderFunctor R) b)
local notation "sa" => CoefficientBassSeedOriginalH0Reference.polynomialIso P pa qa
local notation "sb" => CoefficientBassSeedOriginalH0Reference.polynomialIso P pb qb
local notation "ta" => referenceIso P pa qa
local notation "tb" => referenceIso P pb qb
local notation "delta" => CoefficientBassSeedTerminalPolynomialReference.referenceIso P f α
local notation "kappa" => CoefficientBassSeedTerminalLaurentReference.referenceIso P f α

/-- The original polynomial reference retains source, input and target normalizations. -/
theorem polynomial_transport :
    delta = (isoWhiskerRight sa (M P lf).functor).symm ≪≫
      polynomialTransport P f α ≪≫ isoWhiskerLeft (U).functor sb := by
  simp only [CoefficientBassSeedTerminalPolynomialReference.referenceIso,
    polynomialTransport, isoWhiskerRight_symm, Iso.trans_assoc, coefficientModel, normalizedMap]

/-- The original Laurent reference retains both normalizations around the actual input transport. -/
theorem laurent_transport :
    kappa = (isoWhiskerRight ta (L P lf).functor).symm ≪≫
      laurentTransport P f α ≪≫ isoWhiskerLeft (U).functor tb := by
  simp only [CoefficientBassSeedTerminalLaurentReference.referenceIso,
    CoefficientBassSeedTerminalLaurentReference.targetIso,
    CoefficientBassSeedTargetReferenceTransport.referenceIso, laurentTransport,
    Iso.trans_symm, Iso.symm_symm_eq, isoWhiskerLeft_symm, Iso.trans_assoc]

/-- The ordinary target sheet is precomposed on its genuine source model. -/
def targetOrdinary :
    (U ≫ laurentReference P pb qb).functor ≅
      ((U ≫ polynomialReference P pb qb) ≫ K).functor :=
  isoWhiskerLeft (U).functor (ordinaryAnchor P pb qb) ≪≫
    (Functor.associator (U).functor (polynomialReference P pb qb).functor (K).functor).symm

/-- Both original ordinary anchors agree after their full polynomial and Laurent transports. -/
theorem ordinary_triangle :
    targetAnchor P lf (polynomialReference P pa qa) (laurentReference P pa qa)
        (ordinaryAnchor P pa qa) ≪≫ isoWhiskerRight delta (K).functor =
      kappa ≪≫ targetOrdinary P f α := by
  have hs := CoefficientBassSeedTerminalOrdinaryTriangle.source_normalization P pa qa lf
  have hi := CoefficientBassSeedTerminalInputTriangle.input_triangle P f α
  have ht := CoefficientBassSeedTerminalTargetTriangle.target_normalization P f α
  have h := paste (isoWhiskerRight ta (L P lf).functor)
    (targetAnchor P lf (polynomialReference P pa qa) (laurentReference P pa qa)
      (ordinaryAnchor P pa qa)) _
    (isoWhiskerRight (isoWhiskerRight sa (M P lf).functor) (K).functor)
    (isoWhiskerRight (polynomialTransport P f α) (K).functor)
    (isoWhiskerRight (isoWhiskerLeft (U).functor sb) (K).functor)
    (laurentTransport P f α) (targetAttachment P f α)
    (isoWhiskerLeft (U).functor tb) (targetOrdinary P f α) hs hi ht
  simpa only [polynomial_transport, laurent_transport, isoWhiskerRight_trans,
    isoWhiskerRight_symm] using h

end Quillen.PerfectComplexes.CoefficientBassSeedTerminalAttachmentTriangle
