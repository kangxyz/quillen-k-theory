/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassProjectionFourEdgeTargetTerminalRows
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassProjectionFourEdgeTargetSpanPolynomial
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ProjectionRectangleSquareRows

/-! Both original terminal polynomial rows with their complete target-oriented anchors. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.BassProjectionPath.WholeReference.FourEdge.Target
open BassH0Merge BassH1Join CommonReferenceNerve

private theorem reverse_pair {C : Type*} [Category C] {X Y Z : C}
    (a : X ≅ Y) (b : Z ≅ X) : (a.symm ≪≫ b.symm) ≪≫ (b ≪≫ a) = Iso.refl _ := by
  simp only [Iso.trans_assoc, Iso.symm_self_id_assoc, Iso.symm_self_id]

private theorem post_terminal_node {A B C D : Model.{u}}
    (F : A ⟶ D) (U : A ⟶ B) (J : B ⟶ C) (K : C ⟶ D)
    (S : B ⟶ D) (H : A ⟶ C)
    (α : F.functor ≅ (U ≫ S).functor) (e : S.functor ≅ (J ≫ K).functor)
    (θ : (U ≫ J).functor ≅ H.functor) (η : H.functor ≅ (U ≫ J).functor)
    (h : θ ≪≫ η = Iso.refl _) :
    postReferenceNode F K
      (((α ≪≫ isoWhiskerLeft U.functor e) ≪≫
        (Functor.associator U.functor J.functor K.functor).symm) ≪≫
          isoWhiskerRight θ K.functor) ⟨U ≫ J, η⟩ =
      preReferenceNode F U α ⟨J ≫ K, e⟩ := by
  apply Sigma.ext (Category.assoc U J K)
  apply heq_of_eq
  change (((α ≪≫ isoWhiskerLeft U.functor e) ≪≫
    (Functor.associator U.functor J.functor K.functor).symm) ≪≫
      isoWhiskerRight θ K.functor) ≪≫ isoWhiskerRight η K.functor =
    α ≪≫ isoWhiskerLeft U.functor e
  rw [Iso.trans_assoc, ← isoWhiskerRight_trans, h, isoWhiskerRight_refl]
  erw [Iso.trans_refl]
  change (α ≪≫ isoWhiskerLeft U.functor e) ≪≫ Iso.refl _ = _
  exact Iso.trans_refl _

variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (f : a ⟶ b)
local notation "U" => normalizedMap (coefficientMap P f)
local notation "J" => normalizedMap (polynomialProjection P b)
local notation "F" => BassH0Diagram.reference P f

/-- The target-oriented polynomial anchor cancels the unchanged original terminal square iso. -/
theorem polynomialBaseAnchor_terminal :
    TargetSpan.polynomialSquareBaseAnchor P f ≪≫
      (NativeSquareFiveSimplex.sourceIso
        (coefficientMap P ((polynomialUnderFunctor R).map f)) (polynomialProjection P a)
        (polynomialProjection P b) (coefficientMap P f)
        (coefficientMap_naturality P (polynomialUnderCoefficient R) f) ≪≫
        BinaryNormalizationSimplex.total (polynomialProjection P b) (coefficientMap P f)) =
      Iso.refl _ :=
  reverse_pair (BinaryNormalizationSimplex.total (polynomialProjection P b) (coefficientMap P f))
    (NativeSquareFiveSimplex.sourceIso
      (coefficientMap P ((polynomialUnderFunctor R).map f)) (polynomialProjection P a)
      (polynomialProjection P b) (coefficientMap P f)
      (coefficientMap_naturality P (polynomialUnderCoefficient R) f))

variable (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  (hb : coefficientMap P (α.app b) ≫ polynomialProjection P b = laurentProjection P b)
local notation "K" => normalizedMap (coefficientMap P (α.app b))

/-- The complete target polynomial reference includes both the final chart and square transport. -/
def terminalPolynomialAnchor : (F).functor ≅
    (CoefficientSquareFamilies.polynomialSource P f ≫ K).functor :=
  ((terminalBaseAnchor P f ≪≫
    isoWhiskerLeft (U).functor (BassMJoin.projectionEndpointIso (c := b) P α hb)) ≪≫
      (Functor.associator (U).functor (J).functor (K).functor).symm) ≪≫
        isoWhiskerRight (TargetSpan.polynomialSquareBaseAnchor P f) (K).functor

/-- The terminal full square node is the original target chart endpoint in the H0 reference. -/
theorem terminal_polynomial_endpoint :
    postReferenceNode F K (terminalPolynomialAnchor P f α hb)
      (CoefficientSquareFamilies.polynomialNodes P f 4) =
      preReferenceNode F U (terminalBaseAnchor P f)
        ⟨BassMJoin.endpointMap (c := b) P α, BassMJoin.projectionEndpointIso (c := b) P α hb⟩ := by
  have hs : CoefficientSquareFamilies.polynomialNodes P f 4 =
      (⟨U ≫ J, NativeSquareFiveSimplex.sourceIso
        (coefficientMap P ((polynomialUnderFunctor R).map f)) (polynomialProjection P a)
        (polynomialProjection P b) (coefficientMap P f)
        (coefficientMap_naturality P (polynomialUnderCoefficient R) f) ≪≫
        BinaryNormalizationSimplex.total (polynomialProjection P b) (coefficientMap P f)⟩ :
        CommonReferenceNerve.Node (CoefficientSquareFamilies.polynomialSource P f)) := by
    apply Sigma.ext (Model.Hom.ext rfl)
    exact heq_of_eq rfl
  rw [hs]
  exact post_terminal_node F U J K (BassProjectionPath.source P b)
    (CoefficientSquareFamilies.polynomialSource P f) (terminalBaseAnchor P f)
    (BassMJoin.projectionEndpointIso (c := b) P α hb)
    (TargetSpan.polynomialSquareBaseAnchor P f) _ (polynomialBaseAnchor_terminal P f)

/-- All five positive polynomial nodes agree through their complete shared terminal reference. -/
theorem terminal_polynomial_plus_nodes (i : Fin 5) :
    BassH0Diagram.plusNodes P f (ProjectionRectangleSquareRows.polynomialRow i) =
      postReferenceNode F (normalizedMap (laurentPlus P b))
        (terminalPolynomialAnchor P f (underToLaurent R) (laurentPlus_projection P b))
        (CoefficientSquareFamilies.polynomialNodes P f i) := by
  have h (j : Fin 5) := ProjectionRectangleSquareRows.polynomial_row_nodes
    (polynomialProjection P a) (laurentPlus P a)
    (polynomialProjection P b) (laurentPlus P b)
    (coefficientMap P f) (coefficientMap P ((polynomialUnderFunctor R).map f))
    (coefficientMap P ((laurentUnderFunctor R).map f))
    (coefficientMap_naturality P (polynomialUnderCoefficient R) f)
    (coefficientMap_naturality P (underToLaurent R) f)
    (laurentProjection P a) (laurentPlus_projection P a) j
  have he := (terminal_nodes P f 2).trans
    ((congrArg (preReferenceNode F U (terminalBaseAnchor P f))
      (BassMJoin.plus_endpoint_node (c := b) P)).trans
        (terminal_polynomial_endpoint P f (underToLaurent R) (laurentPlus_projection P b)).symm)
  exact post_families_match F (normalizedMap (laurentPlus P b))
    (CoefficientSquareFamilies.polynomialSource P f) (CoefficientSquareFamilies.polynomialNodes P f)
    h (fun _ ↦ rfl) 4 he i

/-- The inverse polynomial row retains the separate inverse chart and its source transport. -/
theorem terminal_polynomial_minus_nodes (i : Fin 5) :
    BassH0Diagram.minusNodes P f (ProjectionRectangleSquareRows.polynomialRow i) =
      postReferenceNode F (normalizedMap (laurentMinus P b))
        (terminalPolynomialAnchor P f (underToLaurentInvert R) (laurentMinus_projection P b))
        (CoefficientSquareFamilies.polynomialNodes P f i) := by
  have h (j : Fin 5) := ProjectionRectangleSquareRows.polynomial_row_nodes
    (polynomialProjection P a) (laurentMinus P a)
    (polynomialProjection P b) (laurentMinus P b)
    (coefficientMap P f) (coefficientMap P ((polynomialUnderFunctor R).map f))
    (coefficientMap P ((laurentUnderFunctor R).map f))
    (coefficientMap_naturality P (polynomialUnderCoefficient R) f)
    (coefficientMap_naturality P (underToLaurentInvert R) f)
    (laurentProjection P a) (laurentMinus_projection P a) j
  have he := (terminal_nodes P f 4).trans
    ((congrArg (preReferenceNode F U (terminalBaseAnchor P f))
      (BassMJoin.minus_endpoint_node (c := b) P)).trans
        (terminal_polynomial_endpoint P f (underToLaurentInvert R)
          (laurentMinus_projection P b)).symm)
  exact post_families_match F (normalizedMap (laurentMinus P b))
    (CoefficientSquareFamilies.polynomialSource P f) (CoefficientSquareFamilies.polynomialNodes P f)
    h (fun _ ↦ rfl) 4 he i

end Quillen.PerfectComplexes.BassProjectionPath.WholeReference.FourEdge.Target
