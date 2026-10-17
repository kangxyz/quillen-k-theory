/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeConeInputIdentityProduct
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeConeInputLowerParameter

/-! The actual identity input retains both full polynomial chart-square parameters. -/
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
namespace Quillen.PerfectComplexes.BassMWholeConeCarrier.InputActual
open BassH0Merge CommonReferenceNerve CommonReferenceNerve.CutOpenCarrier CommonReferenceProduct
open BassProjectionPath.WholeReference

private theorem chart_identity_word {V W X Y : Type u}
    [Category.{v} V] [Category.{v} W] [Category.{v} X] [Category.{v} Y]
    (A : V ⥤ W) (J : W ⥤ X) (C : X ⥤ Y) (S : W ⥤ Y) (D : V ⥤ X)
    (η : S ≅ J ⋙ C) (k : A ⋙ J ≅ D) :
    isoWhiskerRight (Functor.leftUnitor A).symm S ≪≫
      isoWhiskerLeft ((𝟭 V) ⋙ A) η ≪≫
      isoWhiskerRight (Functor.associator (𝟭 V) A J ≪≫
        isoWhiskerLeft (𝟭 V) k ≪≫ Functor.leftUnitor D) C =
    isoWhiskerLeft A η ≪≫ (Functor.associator A J C).symm ≪≫ isoWhiskerRight k C := by
  apply Iso.ext
  ext x
  simp

private theorem model_comp {U V W : Model.{u}} (F : U ⟶ V) (G : V ⟶ W) :
    (F ≫ G).functor = F.functor ⋙ G.functor := rfl
private theorem model_id (V : Model.{u}) : (𝟙 V : V ⟶ V).functor = 𝟭 V := rfl

variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (p : a ⟶ b)
local notation "A" => normalizedMap (coefficientMap P p)
local notation "D" => CoefficientSquareFamilies.polynomialSource P p
local notation "J" => normalizedMap (polynomialProjection P b)
local notation "Sb" => BassProjectionPath.source P b
local notation "E" => (𝟙 (model P a) ≫ A)
variable (β : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  (hb : coefficientMap P (β.app b) ≫ polynomialProjection P b = laurentProjection P b)
local notation "C" => BassMWholeNerve.coefficientModel P (β.app b)

/-- The complete identity-square chart anchor is the prescribed lower-surface anchor. -/
theorem identity_chart_anchor :
    surfaceIdentity P p ≪≫
      isoWhiskerLeft (E).functor (BassMJoin.projectionEndpointIso P β hb) ≪≫
      isoWhiskerRight (FourEdge.TargetSpan.polynomialSquareAnchor P p (𝟙 (model P a)) ≪≫
        Functor.leftUnitor (D).functor) (C).functor =
      InputPolynomial.lowerSurfaceAnchor P p β hb := by
  have h := chart_identity_word (A).functor (J).functor (C).functor (Sb).functor
    (D).functor (BassMJoin.projectionEndpointIso P β hb)
    (FourEdge.TargetSpan.polynomialSquareBaseAnchor P p)
  rw [polynomial_square_base_anchor] at h
  simpa only [surfaceIdentity, FourEdge.TargetSpan.polynomialSquareAnchor,
    InputPolynomial.lowerSurfaceAnchor, model_comp, model_id, Iso.trans_assoc,
    polynomial_square_base_anchor] using h

/-- Every original polynomial-square node keeps its full chart reference after identity removal. -/
theorem identity_chart_node (N : Node D) :
    reanchor (surfaceIdentity P p) (chartAttachmentNode P b E β hb
      (reanchor (FourEdge.TargetSpan.polynomialSquareAnchor P p (𝟙 (model P a)) ≪≫
        Functor.leftUnitor (D).functor) N)) =
      reanchor (InputPolynomial.lowerSurfaceAnchor P p β hb) (postcompNode C N) := by
  apply Sigma.ext
  · rfl
  apply heq_of_eq
  simp only [chartAttachmentNode, postNode, reanchor, postcompNode,
    isoWhiskerRight_trans, ← Iso.trans_assoc]
  have h := congrArg (fun e ↦ e ≪≫ isoWhiskerRight N.2 (C).functor)
    (identity_chart_anchor P p β hb)
  simpa only [isoWhiskerRight_trans, ← Iso.trans_assoc,
    BassMWholeNerve.coefficientModel, normalizedMap] using h

/-- The entire original chart square retains the same scalar clock and full lower-surface value. -/
theorem identity_chart_parameter (t : I) :
    mapParameter (reanchor (surfaceIdentity P p))
      (mapParameter (chartAttachmentNode P b E β hb)
        (FourEdge.TargetSpan.polynomialSquare P p (𝟙 (model P a))
          (identityParameter P a, t))) =
      InputPolynomial.lowerSurface P p β hb t := by
  rw [polynomial_square_identity]
  change mapParameter _ (mapParameter _ (mapParameter _
    (CommonReferenceNerve.parameter D (CoefficientSquareFamilies.polynomialNodes P p)
      (NativeSquareFiveSimplex.parameter t)))) = _
  rw [mapParameter_parameter, mapParameter_parameter, mapParameter_parameter]
  change _ = mapParameter _ (CommonReferenceNerve.parameter D
    (CoefficientSquareFamilies.polynomialNodes P p) (NativeSquareFiveSimplex.parameter t))
  rw [mapParameter_parameter]
  apply congrArg (fun ns ↦ CommonReferenceNerve.parameter (A ≫ Sb) ns
    (NativeSquareFiveSimplex.parameter t))
  funext i
  exact identity_chart_node P p β hb (CoefficientSquareFamilies.polynomialNodes P p i)

end Quillen.PerfectComplexes.BassMWholeConeCarrier.InputActual
