/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialTripleAnchor
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialLowerNormalization
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialInputBoundaryWord
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassCapChartTripleWord

/-! The whole lower reference of the original input cap retains its right-first transports. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
universe u v
namespace Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialTripleAnchor
open BassReferenceMerge BassH0Merge
local notation "N" => boundedFlatNormalizedPullback
local notation "B" => BinaryNormalizationSimplex.total

private theorem small_refl {C₀ D₀ : Type u} [Category.{v} C₀] [Category.{v} D₀]
    (F : C₀ ⥤ D₀) : smallIso (Iso.refl F) = Iso.refl _ := by
  apply Iso.ext
  ext x
  rfl

private theorem small_eq_symm {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) :
    (smallIso (eqToIso (congrArg N h)) :
      (normalizedMap f).functor ≅ (normalizedMap g).functor).symm =
      smallIso (eqToIso (congrArg N h.symm)) := rfl

private theorem rightFirst_eq {X Y Z T : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) :
    NormalizedTripleSimplex.rightFirst f g h =
      smallIso (eqToIso (congrArg N (Category.assoc f g h).symm)) ≪≫ B (f ≫ g) h :=
  smallIso_trans _ _

private theorem associated_model_word {X Y Z U V W : Scheme.{u}}
    (l : X ⟶ Y) (k : Y ⟶ Z) (ja : Z ⟶ U) (jc : Y ⟶ V)
    (jd : X ⟶ W) (m : W ⟶ V) (h : V ⟶ U)
    (pt : W ⟶ U) (lt : X ⟶ Z) (ep : pt = m ≫ h) (el : lt = l ≫ k)
    (sq₁ : k ≫ ja = jc ≫ h) (sq₂ : l ≫ jc = jd ≫ m)
    (ht : lt ≫ ja = jd ≫ pt) :
    ((isoWhiskerRight (smallIso (eqToIso (congrArg N ep)) ≪≫ B m h)
        (normalizedMap jd).functor ≪≫
      (isoWhiskerLeft (normalizedMap h).functor
        ((B l jc).symm ≪≫ smallIso (eqToIso (congrArg N sq₂)) ≪≫ B jd m)).symm) ≪≫
      isoWhiskerRight ((B jc h).symm ≪≫
        smallIso (eqToIso (congrArg N sq₁.symm)) ≪≫ B k ja)
        (normalizedMap l).functor :
      (normalizedMap pt ≫ normalizedMap jd).functor ≅
        ((normalizedMap ja ≫ normalizedMap k) ≫ normalizedMap l).functor) =
    (B jd pt).symm ≪≫ smallIso (eqToIso (congrArg N ht.symm)) ≪≫ B lt ja ≪≫
      isoWhiskerLeft (normalizedMap ja).functor
        (smallIso (eqToIso (congrArg N el)) ≪≫ B l k) := by
  subst pt lt
  simpa only [eqToIso_refl, small_refl, Iso.refl_trans] using
    CoefficientBassCapChartTripleWord.model_word l k ja jc jd m h sq₁ sq₂ ht

variable {R : CommRingCat.{u}} (P : Over (Spec R))
  (β : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  {a b c d : Under R} (f : a ⟶ b) (p : b ⟶ c) (q : c ⟶ d)

/-- The input cap word retains both original right-first scheme-associativity transports. -/
theorem input_word :
    (isoWhiskerRight (CoefficientBassRaw1PolynomialInputCap.polynomialIso P f p q)
        (normalizedMap (chart P β d)).functor ≪≫
      isoWhiskerLeft (normalizedMap (polynomialArrow P f)).functor
        (CoefficientBassRaw1PolynomialLowerAttachment.lowerAnchor P β p q) ≪≫
      isoWhiskerRight (binaryChartIso P β f).symm
        (normalizedMap (laurentArrow P q ≫ laurentArrow P p)).functor :
      (normalizedMap (polynomialTotal P f p q) ≫ normalizedMap (chart P β d)).functor ≅
        ((normalizedMap (chart P β a) ≫ normalizedMap (laurentArrow P f)) ≫
          normalizedMap (laurentArrow P q ≫ laurentArrow P p)).functor) =
    (referenceIso P β f p q).symm ≪≫
      isoWhiskerLeft (normalizedMap (chart P β a)).functor
        (NormalizedTripleSimplex.rightFirst
          (laurentArrow P q) (laurentArrow P p) (laurentArrow P f)) := by
  have h := associated_model_word
    (laurentArrow P q ≫ laurentArrow P p) (laurentArrow P f)
    (chart P β a) (chart P β b) (chart P β d)
    (polynomialArrow P q ≫ polynomialArrow P p) (polynomialArrow P f)
    (polynomialTotal P f p q) (laurentTotal P f p q)
    (Category.assoc (polynomialArrow P q) (polynomialArrow P p)
      (polynomialArrow P f)).symm
    (Category.assoc (laurentArrow P q) (laurentArrow P p) (laurentArrow P f)).symm
    (coefficientMap_naturality P β f)
    (CoefficientBassRaw1PolynomialLowerNormalization.pair_naturality P β p q).symm
    (total_naturality P β f p q)
  rw [referenceIso_small, binaryChartIso_small,
    CoefficientBassRaw1PolynomialLowerNormalization.lowerAnchor_normalized]
  rw [CoefficientBassRaw1PolynomialInputCap.polynomialIso, rightFirst_eq, rightFirst_eq]
  simp only [Iso.trans_symm, Iso.trans_assoc, Iso.symm_symm_eq,
    isoWhiskerLeft_symm] at h ⊢
  exact h

private theorem precomp_laurent_iso {U V W T : Model.{u}}
    (A : U ⟶ V) (F : V ⟶ W) (F' : U ⟶ W) (J : W ⟶ T)
    (δ : F'.functor ≅ (A ≫ F).functor) :
    CoefficientBassPolynomialSheetNormalization.laurentIso (A ≫ F) F' J
      (A ≫ (F ≫ J))
      (CommonReferenceNerve.CutOpenPrecomp.anchor A F J (F ≫ J) (Iso.refl _)) δ =
      isoWhiskerRight δ J.functor := by
  apply Iso.ext
  apply NatTrans.ext
  funext x
  change J.functor.map (δ.hom.app x) ≫ (𝟙 _ ≫ 𝟙 _) = J.functor.map (δ.hom.app x)
  simp only [Category.comp_id]

local notation "A" => CoefficientBassRaw1ChartCompositionProduct.polynomialInput P f
local notation "F" => CoefficientBassRaw1PolynomialPausedChart.polynomialReference P p q
local notation "J" => BassMWholeNerve.coefficientModel P (β.app d)
local notation "G" => CoefficientBassRaw1PolynomialPausedChart.sheetReference P β p q
local notation "ε" => CommonReferenceNerve.CutOpenPrecomp.anchor A F J G (Iso.refl _)

/-- The actual placed input cap has exactly the whole fixed Laurent right-first anchor. -/
theorem input_anchor :
    CoefficientBassPolynomialSheetNormalization.laurentIso (A ≫ F)
        (polynomialReference P f p q) J (A ≫ G) ε
        (CoefficientBassRaw1PolynomialInputCap.polynomialIso P f p q) ≪≫
      (CoefficientBassRaw1ChartCompositionProduct.midpointIso P β f p q).symm ≪≫
      isoWhiskerRight (CoefficientBassRaw1ChartCompositionProduct.chartNodes P β f 2).2
        (CoefficientBassLaurentCompositionCarrier.reference P p q).functor =
    (referenceIso P β f p q).symm ≪≫
      isoWhiskerLeft (normalizedMap (chart P β a)).functor
        (NormalizedTripleSimplex.rightFirst
          (laurentArrow P q) (laurentArrow P p) (laurentArrow P f)) := by
  have h := congrArg
    (fun e ↦ e ≪≫ (CoefficientBassRaw1ChartCompositionProduct.midpointIso P β f p q).symm ≪≫
      isoWhiskerRight (CoefficientBassRaw1ChartCompositionProduct.chartNodes P β f 2).2
        (CoefficientBassLaurentCompositionCarrier.reference P p q).functor)
    (precomp_laurent_iso A F (polynomialReference P f p q) J
      (CoefficientBassRaw1PolynomialInputCap.polynomialIso P f p q))
  exact h.trans ((input_midpoint_word P β f p q).trans (input_word P β f p q))

end Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialTripleAnchor
