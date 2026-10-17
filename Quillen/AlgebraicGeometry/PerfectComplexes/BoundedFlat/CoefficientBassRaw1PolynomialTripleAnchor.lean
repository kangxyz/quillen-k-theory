/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialPostcomp

/-! The complete chart anchor of the original polynomial triple, before native evaluation. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialTripleAnchor
open BassReferenceMerge
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  (β : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  {a b c d : Under R} (p : a ⟶ b) (q : b ⟶ c) (w : c ⟶ d)

/-- The original coefficient map of a coefficient arrow after polynomial extension. -/
abbrev polynomialArrow {e f : Under R} (k : e ⟶ f) :=
  coefficientMap P ((polynomialUnderFunctor R).map k)
/-- The original coefficient map of a coefficient arrow after Laurent extension. -/
abbrev laurentArrow {e f : Under R} (k : e ⟶ f) :=
  coefficientMap P ((laurentUnderFunctor R).map k)
/-- The original coefficient map of the chosen polynomial-to-Laurent chart at `e`. -/
abbrev chart (e : Under R) := coefficientMap P (β.app e)
/-- The three original polynomial coefficient maps with their prescribed right-first parentheses. -/
abbrev polynomialTotal := polynomialArrow P w ≫ (polynomialArrow P q ≫ polynomialArrow P p)
/-- The three original Laurent coefficient maps with the same right-first parentheses. -/
abbrev laurentTotal := laurentArrow P w ≫ (laurentArrow P q ≫ laurentArrow P p)
/-- The fixed polynomial triple reference of the original postcomposed cap. -/
abbrev polynomialReference := CoefficientBassRaw1PolynomialPostcomp.reference P p q w
/-- The normalized source reference of the original Laurent triple. -/
abbrev laurentReference := NormalizedTripleSimplex.sourceMap
  (laurentArrow P w) (laurentArrow P q) (laurentArrow P p)

/-- Naturality of the original whole three-arrow composite, including its association. -/
theorem total_naturality :
    laurentTotal P p q w ≫ chart P β a = chart P β d ≫ polynomialTotal P p q w := by
  have h := coefficientMap_naturality P β ((p ≫ q) ≫ w)
  simpa only [Functor.map_comp, coefficientMap_comp] using h

/-- The actual fixed-reference chart iso retains both binary totals and equality transport. -/
def referenceIso :
    (BassH0Merge.normalizedMap (chart P β a) ≫ laurentReference P p q w).functor ≅
      (polynomialReference P p q w ≫ BassH0Merge.normalizedMap (chart P β d)).functor :=
  (BinaryNormalizationSimplex.total (laurentTotal P p q w) (chart P β a)).symm ≪≫
    NativeSquareFiveSimplex.sourceIso (laurentTotal P p q w) (chart P β a)
      (chart P β d) (polynomialTotal P p q w) (total_naturality P β p q w) ≪≫
        BinaryNormalizationSimplex.total (chart P β d) (polynomialTotal P p q w)

/-- The actual one-arrow chart transport retains the chosen original naturality square. -/
def binaryChartIso {e f : Under R} (k : e ⟶ f) :
    (BassH0Merge.normalizedMap (chart P β e) ≫
      BassH0Merge.normalizedMap (laurentArrow P k)).functor ≅
    (BassH0Merge.normalizedMap (polynomialArrow P k) ≫
      BassH0Merge.normalizedMap (chart P β f)).functor :=
  (BinaryNormalizationSimplex.total (laurentArrow P k) (chart P β e)).symm ≪≫
    NativeSquareFiveSimplex.sourceIso (laurentArrow P k) (chart P β e)
      (chart P β f) (polynomialArrow P k) (coefficientMap_naturality P β k) ≪≫
        BinaryNormalizationSimplex.total (chart P β f) (polynomialArrow P k)

private theorem flatten_anchor {C₀ A₀ B₀ A₁ B₁ : Type*}
    [Category* C₀] [Category* A₀] [Category* B₀] [Category* A₁] [Category* B₁]
    (F : C₀ ⥤ A₀) (G : C₀ ⥤ B₀) (J : A₀ ⥤ B₀) (L : B₀ ⥤ B₁)
    (H : A₀ ⥤ B₁) (M : A₀ ⥤ A₁) (K : A₁ ⥤ B₁)
    (e : G ≅ F ⋙ J) (lft : H ≅ J ⋙ L) (rgt : H ≅ M ⋙ K) :
    (isoWhiskerRight e L ≪≫ Functor.associator F J L ≪≫
      isoWhiskerLeft F lft.symm) ≪≫ isoWhiskerLeft F rgt ≪≫
        (Functor.associator F M K).symm =
      isoWhiskerRight e L ≪≫ isoWhiskerLeft F (lft.symm ≪≫ rgt) := by
  apply Iso.ext
  ext x
  simp

private theorem flatten_model {V A B A' B' : Model.{u}}
    (F : V ⟶ A) (G : V ⟶ B) (J : A ⟶ B) (L : B ⟶ B')
    (H : A ⟶ B') (M : A ⟶ A') (K : A' ⟶ B')
    (e : G.functor ≅ (F ≫ J).functor)
    (lft : H.functor ≅ (J ≫ L).functor) (rgt : H.functor ≅ (M ≫ K).functor) :
    ((isoWhiskerRight e L.functor ≪≫ Functor.associator F.functor J.functor L.functor ≪≫
      isoWhiskerLeft F.functor lft.symm) ≪≫ isoWhiskerLeft F.functor rgt ≪≫
        (Functor.associator F.functor M.functor K.functor).symm :
          (G ≫ L).functor ≅ ((F ≫ M) ≫ K).functor) =
      isoWhiskerRight e L.functor ≪≫ isoWhiskerLeft F.functor (lft.symm ≪≫ rgt) :=
  flatten_anchor F.functor G.functor J.functor L.functor H.functor M.functor K.functor
    e lft rgt

/-- The plus first-sheet target anchor is the actual complete chart transport. -/
theorem plus_targetAnchor :
    CoefficientBassSeedTargetChartAttachment.targetAnchor P w
      (CoefficientBassRaw1PolynomialPostcomp.pair P p q)
      (CoefficientBassRaw1PolynomialPostcomp.pair P p q ≫
        CoefficientBassSeedTargetChartAttachment.Ja P (a := c)) (Iso.refl _) =
    isoWhiskerLeft (CoefficientBassRaw1PolynomialPostcomp.pair P p q).functor
      (binaryChartIso P (underToLaurent R) w) := by
  have h := flatten_model
    (CoefficientBassRaw1PolynomialPostcomp.pair P p q)
    (CoefficientBassRaw1PolynomialPostcomp.pair P p q ≫
      CoefficientBassSeedTargetChartAttachment.Ja P (a := c))
    (CoefficientBassSeedTargetChartAttachment.Ja P (a := c))
    (CoefficientBassSeedTargetChartAttachment.L P w)
    (CoefficientBassSeedTargetChartAttachment.H P w)
    (CoefficientBassSeedTargetChartAttachment.M P w)
    (CoefficientBassSeedTargetChartAttachment.Jb P (b := d))
    (Iso.refl _) (CoefficientBassSeedTargetChartAttachment.leftIso P w)
    (CoefficientBassSeedTargetChartAttachment.rightIso P w)
  dsimp only [CoefficientBassSeedTargetChartAttachment.targetAnchor,
    CoefficientBassSeedTargetChartAttachment.squareAnchor,
    CoefficientBassSeedTargetChartAttachment.leftIso,
    CoefficientBassSeedTargetChartAttachment.rightIso,
    binaryChartIso, laurentArrow, polynomialArrow, chart, laurentPlus] at h ⊢
  simpa only [isoWhiskerRight_refl, Iso.refl_trans] using h

/-- The minus first-sheet target anchor is the actual complete chart transport. -/
theorem minus_targetAnchor :
    CoefficientBassNegativeTargetChartAttachment.targetAnchor P w
      (CoefficientBassRaw1PolynomialPostcomp.pair P p q)
      (CoefficientBassRaw1PolynomialPostcomp.pair P p q ≫
        CoefficientBassNegativeTargetChartAttachment.Ja P (a := c)) (Iso.refl _) =
    isoWhiskerLeft (CoefficientBassRaw1PolynomialPostcomp.pair P p q).functor
      (binaryChartIso P (underToLaurentInvert R) w) := by
  have h := flatten_model
    (CoefficientBassRaw1PolynomialPostcomp.pair P p q)
    (CoefficientBassRaw1PolynomialPostcomp.pair P p q ≫
      CoefficientBassNegativeTargetChartAttachment.Ja P (a := c))
    (CoefficientBassNegativeTargetChartAttachment.Ja P (a := c))
    (CoefficientBassNegativeTargetChartAttachment.L P w)
    (CoefficientBassNegativeTargetChartAttachment.H P w)
    (CoefficientBassNegativeTargetChartAttachment.M P w)
    (CoefficientBassNegativeTargetChartAttachment.Jb P (b := d))
    (Iso.refl _) (CoefficientBassNegativeTargetChartAttachment.leftIso P w)
    (CoefficientBassNegativeTargetChartAttachment.rightIso P w)
  dsimp only [CoefficientBassNegativeTargetChartAttachment.targetAnchor,
    CoefficientBassNegativeTargetChartAttachment.squareAnchor,
    CoefficientBassNegativeTargetChartAttachment.leftIso,
    CoefficientBassNegativeTargetChartAttachment.rightIso,
    binaryChartIso, laurentArrow, polynomialArrow, chart, laurentMinus] at h ⊢
  simpa only [isoWhiskerRight_refl, Iso.refl_trans] using h

/-- The whole triple chart iso is the small image of the prescribed equality transport. -/
theorem referenceIso_small : referenceIso P β p q w =
    (BinaryNormalizationSimplex.total (laurentTotal P p q w) (chart P β a)).symm ≪≫
      smallIso (eqToIso (congrArg boundedFlatNormalizedPullback
        (total_naturality P β p q w))) ≪≫
      BinaryNormalizationSimplex.total (chart P β d) (polynomialTotal P p q w) := by
  rw [smallIso_eqToIso]
  rfl

/-- The actual binary square retains its complete raw equality transport under normalization. -/
theorem binaryChartIso_small {e f : Under R} (k : e ⟶ f) : binaryChartIso P β k =
    (BinaryNormalizationSimplex.total (laurentArrow P k) (chart P β e)).symm ≪≫
      smallIso (eqToIso (congrArg boundedFlatNormalizedPullback
        (coefficientMap_naturality P β k))) ≪≫
      BinaryNormalizationSimplex.total (chart P β f) (polynomialArrow P k) := by
  rw [smallIso_eqToIso]
  rfl

end Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialTripleAnchor
