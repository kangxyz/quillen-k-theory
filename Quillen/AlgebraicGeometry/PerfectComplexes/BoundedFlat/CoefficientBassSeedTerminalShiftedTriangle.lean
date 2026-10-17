/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSeedTerminalAttachmentTriangle

/-! The terminal shifted sheet retains the original full inner Laurent unit. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor
open Quillen.Waldhausen.IteratedS Quillen.FunctorIdentityAutomorphism
universe u
namespace Quillen.PerfectComplexes.CoefficientBassSeedTerminalShiftedTriangle

private theorem action_precomp {V W T : Model.{u}} (U : V ⟶ W) (G : W ⟶ T)
    (e : 𝟭 T.category ≅ 𝟭 T.category) :
    onFunctor (U ≫ G).functor e = isoWhiskerLeft U.functor (onFunctor G.functor e) := by
  apply Iso.ext
  ext x
  rfl

private theorem inverse_intertwine {C : Type u} [Category C] {X Y : C}
    (k : X ≅ Y) (a : X ≅ X) (b : Y ≅ Y)
    (h : b ≪≫ k.symm = k.symm ≪≫ a) : a ≪≫ k = k ≪≫ b := by
  have hh := congrArg (fun e ↦ k ≪≫ e ≪≫ k) h
  simpa only [Iso.trans_assoc, Iso.self_symm_id_assoc, Iso.symm_self_id,
    Iso.trans_refl] using hh.symm

open AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open BassH0Merge BassMWholeNerve
open LaurentUnitReferenceSpecialization (commonUnit commonUnit_eq_action)
open CoefficientBassPositiveC1BoundaryLift CoefficientBassSeedTargetChartAttachment
open CoefficientBassSeedTerminalAttachmentTriangle
variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (f : a ⟶ b)
  (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
local notation "pa" => CategoryTheory.NatTrans.app (polynomialUnderCoefficient R) a
local notation "qa" => CategoryTheory.NatTrans.app α a
local notation "pb" => CategoryTheory.NatTrans.app (polynomialUnderCoefficient R) b
local notation "qb" => CategoryTheory.NatTrans.app α b
local notation "lf" => CategoryTheory.Functor.map (laurentUnderFunctor R) f
local notation "U" => coefficientModel P f
local notation "K" => Jb P (b := CategoryTheory.Functor.obj (laurentUnderFunctor R) b)
local notation "delta" => CoefficientBassSeedTerminalPolynomialReference.referenceIso P f α
local notation "kappa" => CoefficientBassSeedTerminalLaurentReference.referenceIso P f α

/-- The actual terminal Laurent transport intertwines the two prescribed total units. -/
theorem unit_transport :
    isoWhiskerRight (commonUnit P pa qa) (L P lf).functor ≪≫ kappa =
      kappa ≪≫ isoWhiskerLeft (U).functor (commonUnit P pb qb) := by
  have h := CoefficientBassSeedTerminalLaurentReference.unit_intertwine P f α
  dsimp only [CoefficientBassSeedTerminalLaurentReference.targetReference] at h
  rw [action_precomp] at h
  rw [← commonUnit_eq_action, ← commonUnit_eq_action] at h
  exact inverse_intertwine kappa _ _ h

/-- The target shifted sheet uses the same original unit before its ordinary attachment. -/
def targetShifted :
    (U ≫ laurentReference P pb qb).functor ≅
      ((U ≫ polynomialReference P pb qb) ≫ K).functor :=
  isoWhiskerLeft (U).functor (commonUnit P pb qb ≪≫ ordinaryAnchor P pb qb) ≪≫
    (Functor.associator (U).functor (polynomialReference P pb qb).functor (K).functor).symm

/-- The complete shifted attachment commutes with the original polynomial and Laurent transports. -/
theorem shifted_triangle :
    targetAnchor P lf (polynomialReference P pa qa) (laurentReference P pa qa)
        (commonUnit P pa qa ≪≫ ordinaryAnchor P pa qa) ≪≫
      isoWhiskerRight delta (K).functor = kappa ≪≫ targetShifted P f α := by
  rw [targetAnchor_shifted, Iso.trans_assoc, ordinary_triangle,
    ← Iso.trans_assoc, unit_transport]
  simp only [targetShifted, targetOrdinary, isoWhiskerLeft_trans, Iso.trans_assoc]

end Quillen.PerfectComplexes.CoefficientBassSeedTerminalShiftedTriangle
