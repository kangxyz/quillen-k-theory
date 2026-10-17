/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSeedTerminalChartJoin
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSeedTargetH0Chart
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSeedTerminalPolynomialReference
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.NativeSquareModelNormalization

/-! The actual terminal chart anchor after the original H0 projection transport. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.CoefficientBassSeedTerminalBaseTriangle
open BassH0Merge CoefficientBassSeedTargetChartAttachment CoefficientBassSeedTargetH0Reference
open BassProjectionPath.WholeReference.FourEdge.Target
/-- A full polynomial anchor with its composite model endpoint fixed before specialization. -/
def postAnchor {A B C D : Model.{u}} (S : A ⟶ D) (F : A ⟶ C)
    (J : A ⟶ B) (M : B ⟶ C) (K : C ⟶ D)
    (θ : S.functor ≅ (F ≫ K).functor) (t : F.functor ≅ (J ≫ M).functor) :
    S.functor ≅ ((J ≫ M) ≫ K).functor := θ ≪≫ isoWhiskerRight t K.functor

private theorem node_anchor {A B C D : Model.{u}} (S : A ⟶ D) (F : A ⟶ C)
    (H : B ⟶ D) (J : A ⟶ B) (M : B ⟶ C) (K : C ⟶ D)
    (γ : S.functor ≅ (J ≫ H).functor) (r : H.functor ≅ (M ≫ K).functor)
    (θ : S.functor ≅ (F ≫ K).functor) (t : F.functor ≅ (J ≫ M).functor)
    (hn : BassH0Merge.preReferenceNode S J γ ⟨M ≫ K, r⟩ =
      BassH1Join.postReferenceNode S K θ ⟨J ≫ M, t⟩) :
    ((γ ≪≫ isoWhiskerLeft J.functor r) ≪≫
      (Functor.associator J.functor M.functor K.functor).symm :
      S.functor ≅ ((J ≫ M) ≫ K).functor) = postAnchor S F J M K θ t := by
  have h := eq_of_heq (Sigma.mk.inj hn).2
  have ha : Functor.associator J.functor M.functor K.functor = Iso.refl _ := rfl
  rw [ha, Iso.refl_symm]
  erw [Iso.trans_refl]
  exact h

private theorem cancel_model {A B C D E : Model.{u}}
    (J : A ⟶ B) (K : B ⟶ C) (L : C ⟶ D) (M : B ⟶ E) (N : E ⟶ D)
    (F : A ⟶ C) (G : A ⟶ D) (H : B ⟶ D)
    (ε : F.functor ≅ (J ≫ K).functor) (h : G.functor ≅ (F ≫ L).functor)
    (l : H.functor ≅ (K ≫ L).functor) (r : H.functor ≅ (M ≫ N).functor)
    (a : G.functor ≅ (J ≫ H).functor)
    (hh : h ≪≫ isoWhiskerRight ε L.functor = a ≪≫ isoWhiskerLeft J.functor l) :
    (h ≪≫ ((isoWhiskerRight ε L.functor ≪≫
      Functor.associator J.functor K.functor L.functor ≪≫
      isoWhiskerLeft J.functor l.symm) ≪≫ isoWhiskerLeft J.functor r ≪≫
        (Functor.associator J.functor M.functor N.functor).symm) :
      G.functor ≅ ((J ≫ M) ≫ N).functor) =
      (a ≪≫ isoWhiskerLeft J.functor r) ≪≫
        (Functor.associator J.functor M.functor N.functor).symm :=
  NativeSquareModelNormalization.whiskered_cancel J.functor K.functor L.functor M.functor
    N.functor F.functor G.functor H.functor ε h l r a hh

variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (f : a ⟶ b)
local notation "J" => Model.Hom.functor (normalizedMap (polynomialProjection P a))
local notation "L₀" => Model.Hom.functor (L P f)
local notation "M₀" => Model.Hom.functor (M P f)
local notation "K₀" => Model.Hom.functor (Jb P (b := b))
local notation "l" => NativeSquareModelNormalization.total
  (coefficientMap P (CategoryTheory.Functor.map (laurentUnderFunctor R) f)) (laurentPlus P a)
local notation "r" => NativeSquareModelNormalization.rightIso
  (coefficientMap P (CategoryTheory.Functor.map (laurentUnderFunctor R) f)) (laurentPlus P a)
  (laurentPlus P b) (coefficientMap P (CategoryTheory.Functor.map (polynomialUnderFunctor R) f))
  (coefficientMap_naturality P (underToLaurent R) f)
local notation "t" => NativeSquareModelNormalization.total
  (coefficientMap P (CategoryTheory.Functor.map (polynomialUnderFunctor R) f))
  (polynomialProjection P a)
local notation "γ" => ProjectionRectangleSquareRows.chartAnchor (polynomialProjection P a)
  (laurentPlus P a)
  (coefficientMap P (CategoryTheory.Functor.map (laurentUnderFunctor R) f))
  (laurentProjection P a) (laurentPlus_projection P a)
local notation "ε" => BassMJoin.projectionEndpointIso P (underToLaurent R)
  (laurentPlus_projection P a)
local notation "θ" => terminalPolynomialAnchor P f (underToLaurent R)
  (laurentPlus_projection P b)

/-- The original polynomial total with its named model aliases normalized explicitly. -/
def polynomialTotal : (CoefficientSquareFamilies.polynomialSource P f).functor ≅
    (normalizedMap (polynomialProjection P a) ≫ M P f).functor := by
  dsimp only [CoefficientSquareFamilies.polynomialSource, NativeSquareFiveSimplex.source, M]
  exact t

/-- The original chart right word with its named model aliases normalized explicitly. -/
def chartRight : (H P f).functor ≅ (M P f ≫ Jb P (b := b)).functor := by
  dsimp only [H, M, Jb, NativeSquareFiveSimplex.source]
  exact r

/-- The original terminal polynomial-square anchor with its exact composite model endpoint. -/
def terminalAnchor : (BassH0Diagram.reference P f).functor ≅
    ((normalizedMap (polynomialProjection P a) ≫ M P f) ≫ Jb P (b := b)).functor :=
  postAnchor (BassH0Diagram.reference P f) (CoefficientSquareFamilies.polynomialSource P f)
    (normalizedMap (polynomialProjection P a)) (M P f) (Jb P (b := b)) θ (polynomialTotal P f)

private theorem terminal_anchor :
    ((γ ≪≫ isoWhiskerLeft J (chartRight P f)) ≪≫ (Functor.associator J M₀ K₀).symm :
      (BassH0Diagram.reference P f).functor ≅
        ((normalizedMap (polynomialProjection P a) ≫ M P f) ≫ Jb P (b := b)).functor) =
      terminalAnchor P f := by
  have hn := CoefficientBassSeedTerminalChartJoin.positive_node P f
  dsimp only [BassH0ChartBoundaryRows.squareNodes, CoefficientSquareFamilies.polynomialNodes]
    at hn
  rw [NativeSquareModelNormalization.nodes_four, NativeSquareModelNormalization.nodes_two] at hn
  exact node_anchor (BassH0Diagram.reference P f)
    (CoefficientSquareFamilies.polynomialSource P f) (H P f)
    (normalizedMap (polynomialProjection P a)) (M P f) (Jb P (b := b))
    γ (chartRight P f) θ (polynomialTotal P f) hn

/-- The original H0 target attachment retains the explicitly normalized terminal model endpoint. -/
theorem h0_target_anchor :
    h0ProjectionIso P f ≪≫ targetAnchor P f
      (normalizedMap (polynomialProjection P a)) (BassProjectionPath.source P a) ε =
    terminalAnchor P f := by
  have hh := CoefficientBassSeedTargetH0Chart.h0_chart_total P f
  have hw := cancel_model (normalizedMap (polynomialProjection P a)) (Ja P (a := a))
    (L P f) (M P f) (Jb P (b := b)) (BassProjectionPath.source P a)
    (BassH0Diagram.reference P f) (H P f) ε (h0ProjectionIso P f)
    (leftIso P f) (chartRight P f) γ hh
  rw [terminal_anchor P f] at hw
  simpa only [targetAnchor, squareAnchor, NativeSquareModelNormalization.total_original,
    NativeSquareModelNormalization.rightIso_original, chartRight, rightIso, id_eq] using hw

end Quillen.PerfectComplexes.CoefficientBassSeedTerminalBaseTriangle
