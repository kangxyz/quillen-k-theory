/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSeedTerminalShiftedTriangle
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceReanchorAttachment

/-! Both original terminal attachments agree on their complete reference nerves. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology
universe u
namespace Quillen.PerfectComplexes.CoefficientBassSeedTerminalAttachmentNodes
open CommonReferenceNerve CommonReferenceProduct

private theorem attachment_node {V W T : Model.{u}} (F F' : V ⟶ W) (J : W ⟶ T)
    (G G' : V ⟶ T) (δ : F.functor ≅ F'.functor) (κ : G.functor ≅ G'.functor)
    (ε : G.functor ≅ (F ≫ J).functor) (η : G'.functor ≅ (F' ≫ J).functor)
    (h : ε ≪≫ isoWhiskerRight δ J.functor = κ ≪≫ η) (N : Node F') :
    reanchor κ (attachPostcompNode F' J G' η N) =
      attachPostcompNode F J G ε (reanchor δ N) := by
  rcases N with ⟨K, ρ⟩
  change (⟨K ≫ J, κ ≪≫ (η ≪≫ isoWhiskerRight ρ J.functor)⟩ : Node G) =
    ⟨K ≫ J, ε ≪≫ isoWhiskerRight (δ ≪≫ ρ) J.functor⟩
  apply congrArg (fun e : G.functor ≅ (K ≫ J).functor ↦ (⟨K ≫ J, e⟩ : Node G))
  simpa only [isoWhiskerRight_trans, Iso.trans_assoc] using
    congrArg (fun e ↦ e ≪≫ isoWhiskerRight ρ J.functor) h.symm

open BassH0Merge BassMWholeNerve
open LaurentUnitReferenceSpecialization (commonUnit)
open CoefficientBassPositiveC1BoundaryLift CoefficientBassSeedTargetChartAttachment
open CoefficientBassSeedTerminalAttachmentTriangle CoefficientBassSeedTerminalShiftedTriangle
variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (f : a ⟶ b)
  (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
local notation "pa" => CategoryTheory.NatTrans.app (polynomialUnderCoefficient R) a
local notation "qa" => CategoryTheory.NatTrans.app α a
local notation "pb" => CategoryTheory.NatTrans.app (polynomialUnderCoefficient R) b
local notation "qb" => CategoryTheory.NatTrans.app α b
local notation "lf" => CategoryTheory.Functor.map (laurentUnderFunctor R) f
local notation "U" => coefficientModel P f
local notation "K" => Jb P (b := CategoryTheory.Functor.obj (laurentUnderFunctor R) b)

/-- The target chosen polynomial sheet on the genuine original input model. -/
abbrev sourcePolynomial := U ≫ polynomialReference P pb qb
/-- The target chosen Laurent reference on the genuine original input model. -/
abbrev sourceLaurent := U ≫ laurentReference P pb qb
/-- The post-action polynomial reference retains the original source sheet. -/
abbrev targetPolynomial := polynomialReference P pa qa ≫ M P lf
/-- The post-action Laurent reference retains the original source reference. -/
abbrev targetLaurent := laurentReference P pa qa ≫ L P lf

/-- The ordinary target anchor uses the original moving chart square. -/
abbrev ordinary := targetAnchor P lf (polynomialReference P pa qa)
  (laurentReference P pa qa) (ordinaryAnchor P pa qa)
/-- The shifted target anchor uses the same moving square with the original inner unit. -/
abbrev shifted := targetAnchor P lf (polynomialReference P pa qa)
  (laurentReference P pa qa) (commonUnit P pa qa ≪≫ ordinaryAnchor P pa qa)

/-- The complete ordinary node square retains both actual normalization transports. -/
theorem ordinary_node (N : Node (sourcePolynomial P f α)) :
    reanchor (CoefficientBassSeedTerminalLaurentReference.referenceIso P f α)
      (attachPostcompNode (sourcePolynomial P f α) K (sourceLaurent P f α)
        (targetOrdinary P f α) N) =
    attachPostcompNode (targetPolynomial P f α) K (targetLaurent P f α) (ordinary P f α)
      (reanchor (CoefficientBassSeedTerminalPolynomialReference.referenceIso P f α) N) :=
  attachment_node _ _ _ _ _ _ _ _ _ (ordinary_triangle P f α) N

/-- The complete shifted node square retains the full original inner Laurent unit. -/
theorem shifted_node (N : Node (sourcePolynomial P f α)) :
    reanchor (CoefficientBassSeedTerminalLaurentReference.referenceIso P f α)
      (attachPostcompNode (sourcePolynomial P f α) K (sourceLaurent P f α)
        (targetShifted P f α) N) =
    attachPostcompNode (targetPolynomial P f α) K (targetLaurent P f α) (shifted P f α)
      (reanchor (CoefficientBassSeedTerminalPolynomialReference.referenceIso P f α) N) :=
  attachment_node _ _ _ _ _ _ _ _ _ (shifted_triangle P f α) N

/-- The entire ordinary parameter attachment commutes at every point of the nerve. -/
theorem ordinary_parameter (y : |nerve (Codiscrete (Node (sourcePolynomial P f α)))|) :
    mapParameter (reanchor (CoefficientBassSeedTerminalLaurentReference.referenceIso P f α))
      (mapParameter (attachPostcompNode (sourcePolynomial P f α) K (sourceLaurent P f α)
        (targetOrdinary P f α)) y) =
    mapParameter (attachPostcompNode (targetPolynomial P f α) K (targetLaurent P f α)
      (ordinary P f α))
      (mapParameter (reanchor
        (CoefficientBassSeedTerminalPolynomialReference.referenceIso P f α)) y) := by
  obtain ⟨k, ns, z, rfl⟩ := exists_parameter (sourcePolynomial P f α) y
  erw [mapParameter_parameter, mapParameter_parameter,
    mapParameter_parameter, mapParameter_parameter]
  exact congrArg (fun nodes ↦ parameter (targetLaurent P f α) nodes z)
    (funext fun i ↦ ordinary_node P f α (ns i))

/-- The entire shifted parameter attachment commutes with the same original unit word. -/
theorem shifted_parameter (y : |nerve (Codiscrete (Node (sourcePolynomial P f α)))|) :
    mapParameter (reanchor (CoefficientBassSeedTerminalLaurentReference.referenceIso P f α))
      (mapParameter (attachPostcompNode (sourcePolynomial P f α) K (sourceLaurent P f α)
        (targetShifted P f α)) y) =
    mapParameter (attachPostcompNode (targetPolynomial P f α) K (targetLaurent P f α)
      (shifted P f α))
      (mapParameter (reanchor
        (CoefficientBassSeedTerminalPolynomialReference.referenceIso P f α)) y) := by
  obtain ⟨k, ns, z, rfl⟩ := exists_parameter (sourcePolynomial P f α) y
  erw [mapParameter_parameter, mapParameter_parameter,
    mapParameter_parameter, mapParameter_parameter]
  exact congrArg (fun nodes ↦ parameter (targetLaurent P f α) nodes z)
    (funext fun i ↦ shifted_node P f α (ns i))

end Quillen.PerfectComplexes.CoefficientBassSeedTerminalAttachmentNodes
