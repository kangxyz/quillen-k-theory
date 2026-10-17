/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialTripleAnchor
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialLowerNormalization
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassCapChartTripleWord

/-! The whole lower reference of the postcomposed cap is the prescribed Laurent reference. -/
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
open BassReferenceMerge
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  (β : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  {a b c d : Under R} (p : a ⟶ b) (q : b ⟶ c) (w : c ⟶ d)

private theorem small_symm {C D : Type u} [Category.{v} C] [Category.{v} D]
    {F G : C ⥤ D} (e : F ≅ G) : (smallIso e).symm = smallIso e.symm := rfl

private theorem eq_iso_symm {C : Type*} [Category C] {X Y : C} (h : X = Y) :
    (eqToIso h).symm = eqToIso h.symm := by
  subst Y
  rfl

private theorem left_first_total {X Y Z T : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) :
    NormalizedTripleSimplex.leftFirst f g h = BinaryNormalizationSimplex.total f (g ≫ h) := rfl

private theorem binary_source_normalized {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    BinaryNormalizationSimplex.sourceMap f g = BassH0Merge.normalizedMap (f ≫ g) := rfl

/-- The postcomposed old cap and the fixed Laurent triple have identical full lower anchors. -/
theorem postcomp_word :
    ((isoWhiskerRight (CoefficientBassRaw1PolynomialPostcomp.polynomialIso P p q w)
        (BassH0Merge.normalizedMap (chart P β d)).functor ≪≫
      (isoWhiskerLeft (CoefficientBassRaw1PolynomialPostcomp.pair P p q).functor
        (binaryChartIso P β w)).symm) ≪≫
      isoWhiskerRight (CoefficientBassRaw1PolynomialLowerAttachment.lowerAnchor P β p q)
        (BassH0Merge.normalizedMap (laurentArrow P w)).functor :
      (BassH0Merge.normalizedMap (polynomialTotal P p q w) ≫
        BassH0Merge.normalizedMap (chart P β d)).functor ≅
      ((BassH0Merge.normalizedMap (chart P β a) ≫
        BassH0Merge.normalizedMap (laurentArrow P q ≫ laurentArrow P p)) ≫
        BassH0Merge.normalizedMap (laurentArrow P w)).functor) =
    (referenceIso P β p q w).symm ≪≫
      isoWhiskerLeft (BassH0Merge.normalizedMap (chart P β a)).functor
        (NormalizedTripleSimplex.leftFirst
          (laurentArrow P w) (laurentArrow P q) (laurentArrow P p)) := by
  have h := CoefficientBassCapChartTripleWord.model_word
    (laurentArrow P w) (laurentArrow P q ≫ laurentArrow P p)
    (chart P β a) (chart P β c) (chart P β d)
    (polynomialArrow P w) (polynomialArrow P q ≫ polynomialArrow P p)
    (CoefficientBassRaw1PolynomialLowerNormalization.pair_naturality P β p q).symm
    (coefficientMap_naturality P β w) (total_naturality P β p q w)
  rw [referenceIso_small, binaryChartIso_small,
    CoefficientBassRaw1PolynomialLowerNormalization.lowerAnchor_normalized]
  rw [CoefficientBassRaw1PolynomialPostcomp.polynomialIso, left_first_total,
    left_first_total]
  have hi :
      (smallIso (eqToIso (congrArg boundedFlatNormalizedPullback
        (total_naturality P β p q w)))).symm =
      smallIso (eqToIso (congrArg boundedFlatNormalizedPullback
        (total_naturality P β p q w).symm)) := rfl
  simp only [Iso.trans_symm, Iso.trans_assoc, Iso.symm_symm_eq] at h ⊢
  rw [hi]
  dsimp only [CoefficientBassRaw1PolynomialPostcomp.firstArrow,
    CoefficientBassRaw1PolynomialPostcomp.secondArrow,
    CoefficientBassRaw1PolynomialPostcomp.lastArrow,
    CoefficientBassRaw1PolynomialPostcomp.pair,
    CoefficientBassRaw1PolynomialPausedChart.polynomialReference,
    polynomialTotal, laurentTotal, chart, polynomialArrow, laurentArrow] at h ⊢
  simp only [binary_source_normalized]
  exact h

/-- The actual plus placement retains this full lower anchor before evaluation. -/
theorem plus_postcomp_anchor :
    CoefficientBassPolynomialSheetNormalization.laurentIso
      (CoefficientBassRaw1PolynomialPostcomp.pair P p q ≫
        CoefficientBassSeedTargetChartAttachment.M P w)
      (polynomialReference P p q w) (CoefficientBassSeedTargetChartAttachment.Jb P (b := d))
      ((CoefficientBassRaw1PolynomialPostcomp.pair P p q ≫
        CoefficientBassSeedTargetChartAttachment.Ja P (a := c)) ≫
        CoefficientBassSeedTargetChartAttachment.L P w)
      (CoefficientBassSeedTargetChartAttachment.targetAnchor P w
        (CoefficientBassRaw1PolynomialPostcomp.pair P p q)
        (CoefficientBassRaw1PolynomialPostcomp.pair P p q ≫
          CoefficientBassSeedTargetChartAttachment.Ja P (a := c)) (Iso.refl _))
      (CoefficientBassRaw1PolynomialPostcomp.polynomialIso P p q w) ≪≫
      isoWhiskerRight (CoefficientBassRaw1PolynomialLowerAttachment.lowerAnchor
        P (underToLaurent R) p q) (CoefficientBassSeedTargetChartAttachment.L P w).functor =
    (referenceIso P (underToLaurent R) p q w).symm ≪≫
      isoWhiskerLeft (BassH0Merge.normalizedMap (chart P (underToLaurent R) a)).functor
        (NormalizedTripleSimplex.leftFirst
          (laurentArrow P w) (laurentArrow P q) (laurentArrow P p)) := by
  dsimp only [CoefficientBassPolynomialSheetNormalization.laurentIso]
  rw [plus_targetAnchor]
  exact postcomp_word P (underToLaurent R) p q w

/-- The actual minus placement retains this full lower anchor before evaluation. -/
theorem minus_postcomp_anchor :
    CoefficientBassPolynomialSheetNormalization.laurentIso
      (CoefficientBassRaw1PolynomialPostcomp.pair P p q ≫
        CoefficientBassNegativeTargetChartAttachment.M P w)
      (polynomialReference P p q w) (CoefficientBassNegativeTargetChartAttachment.Jb P (b := d))
      ((CoefficientBassRaw1PolynomialPostcomp.pair P p q ≫
        CoefficientBassNegativeTargetChartAttachment.Ja P (a := c)) ≫
        CoefficientBassNegativeTargetChartAttachment.L P w)
      (CoefficientBassNegativeTargetChartAttachment.targetAnchor P w
        (CoefficientBassRaw1PolynomialPostcomp.pair P p q)
        (CoefficientBassRaw1PolynomialPostcomp.pair P p q ≫
          CoefficientBassNegativeTargetChartAttachment.Ja P (a := c)) (Iso.refl _))
      (CoefficientBassRaw1PolynomialPostcomp.polynomialIso P p q w) ≪≫
      isoWhiskerRight (CoefficientBassRaw1PolynomialLowerAttachment.lowerAnchor
        P (underToLaurentInvert R) p q)
        (CoefficientBassNegativeTargetChartAttachment.L P w).functor =
    (referenceIso P (underToLaurentInvert R) p q w).symm ≪≫
      isoWhiskerLeft (BassH0Merge.normalizedMap (chart P (underToLaurentInvert R) a)).functor
        (NormalizedTripleSimplex.leftFirst
          (laurentArrow P w) (laurentArrow P q) (laurentArrow P p)) := by
  dsimp only [CoefficientBassPolynomialSheetNormalization.laurentIso]
  rw [minus_targetAnchor]
  exact postcomp_word P (underToLaurentInvert R) p q w

end Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialTripleAnchor
