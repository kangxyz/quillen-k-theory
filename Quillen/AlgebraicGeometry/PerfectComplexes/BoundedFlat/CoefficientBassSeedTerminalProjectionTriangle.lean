/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSeedTerminalBaseTriangle

/-! Cancellation of the original polynomial projection normalizations
in the terminal seed anchor. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.CoefficientBassSeedTerminalProjectionTriangle
open BassH0Merge CoefficientBassSeedTargetChartAttachment CoefficientBassSeedTargetH0Reference
open CoefficientBassSeedTerminalBaseTriangle
open BassProjectionPath.WholeReference.FourEdge
open BassProjectionPath.WholeReference.FourEdge.Target

private theorem inverse_source {X Y Z T : Scheme.{u}} (p : X ⟶ Y) (v : Y ⟶ Z)
    (q : X ⟶ T) (w : T ⟶ Z) (h : p ≫ v = q ≫ w) :
    (NativeSquareFiveSimplex.sourceIso p v q w h).symm =
      eqToIso (congrArg (fun g ↦ (normalizedMap g).functor) h.symm) := by
  apply Iso.ext
  rfl

private theorem cancel_projected {V C D : Model.{u}}
    (F G H : V ⟶ C) (K : C ⟶ D) (X Y Z W : V ⟶ D)
    (a : X.functor ≅ Y.functor) (q : Y.functor ≅ Z.functor)
    (e : Z.functor ≅ W.functor) (s : W.functor ≅ (F ≫ K).functor)
    (b : F.functor ≅ G.functor) (t : G.functor ≅ H.functor)
    (r : F.functor ≅ H.functor) (k : Y.functor ≅ (H ≫ K).functor)
    (hr : b ≪≫ t = r)
    (hk : a ≪≫ k = ((((a ≪≫ q) ≪≫ e) ≪≫ s) ≪≫
      isoWhiskerRight b K.functor) ≪≫ isoWhiskerRight t K.functor) :
    k = q ≪≫ e ≪≫ s ≪≫ isoWhiskerRight r K.functor := by
  have h := congrArg (fun z ↦ a.symm ≪≫ z) hk
  simp only [Iso.trans_assoc, Iso.symm_self_id_assoc] at h
  rw [← isoWhiskerRight_trans, hr] at h
  exact h

variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (f : a ⟶ b)

/-- The two original polynomial normalizations are precisely the projection reference transport. -/
theorem polynomial_total :
    TargetSpan.polynomialSquareBaseAnchor P f ≪≫ polynomialTotal P f =
      CoefficientBassSeedTerminalPolynomialReference.projectionIso P f := by
  simp only [TargetSpan.polynomialSquareBaseAnchor, polynomialTotal, id_eq,
    NativeSquareModelNormalization.total_original, inverse_source,
    CoefficientBassSeedTerminalPolynomialReference.projectionIso, Iso.trans_assoc]

/-- The original chart target anchor expressed through both complete projection transports. -/
def projectionAnchor :
    (BassProjectionPath.source P a ≫ L P f).functor ≅
      ((normalizedMap (polynomialProjection P a) ≫ M P f) ≫ Jb P (b := b)).functor :=
  (CoefficientBassSeedTargetReferenceTransport.projectionIso P f).symm ≪≫
    isoWhiskerLeft (normalizedMap (coefficientMap P f)).functor
      (BassMJoin.projectionEndpointIso P (underToLaurent R) (laurentPlus_projection P b)) ≪≫
    (Functor.associator (normalizedMap (coefficientMap P f)).functor
      (normalizedMap (polynomialProjection P b)).functor (Jb P (b := b)).functor).symm ≪≫
    isoWhiskerRight (CoefficientBassSeedTerminalPolynomialReference.projectionIso P f)
      (Jb P (b := b)).functor

/-- The H0 node join yields the full actual projection triangle without changing either sheet. -/
theorem target_anchor :
    targetAnchor P f (normalizedMap (polynomialProjection P a)) (BassProjectionPath.source P a)
      (BassMJoin.projectionEndpointIso P (underToLaurent R) (laurentPlus_projection P a)) =
        projectionAnchor P f := by
  apply cancel_projected
    (normalizedMap (coefficientMap P f) ≫ normalizedMap (polynomialProjection P b))
    (CoefficientSquareFamilies.polynomialSource P f)
    (normalizedMap (polynomialProjection P a) ≫ M P f) (Jb P (b := b))
    (BassH0Diagram.reference P f) (BassProjectionPath.source P a ≫ L P f)
    (normalizedMap (coefficientMap P f) ≫ BassProjectionPath.source P b)
    (normalizedMap (coefficientMap P f) ≫
      (normalizedMap (polynomialProjection P b) ≫ Jb P (b := b)))
    (h0ProjectionIso P f) (CoefficientBassSeedTargetReferenceTransport.projectionIso P f).symm
    (isoWhiskerLeft (normalizedMap (coefficientMap P f)).functor
      (BassMJoin.projectionEndpointIso P (underToLaurent R) (laurentPlus_projection P b)))
    (Functor.associator (normalizedMap (coefficientMap P f)).functor
      (normalizedMap (polynomialProjection P b)).functor (Jb P (b := b)).functor).symm
    (TargetSpan.polynomialSquareBaseAnchor P f) (polynomialTotal P f)
    (CoefficientBassSeedTerminalPolynomialReference.projectionIso P f) _ (polynomial_total P f)
  simpa only [terminalAnchor, postAnchor, terminalPolynomialAnchor, terminalBaseAnchor,
    Jb, AlgebraicGeometry.Scheme.BaseChange.Coefficients.laurentPlus] using
    h0_target_anchor P f

end Quillen.PerfectComplexes.CoefficientBassSeedTerminalProjectionTriangle
