/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialPostcomp
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialPairCorrected

/-! The original postcomposed cap retains its entire Laurent face before evaluation. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes
open CommonReferenceNerve CommonReferenceNerve.CutOpenCarrier

namespace CoefficientBassPolynomialSheetNormalization
/-- The exact first-sheet normalization on the full Laurent summand. -/
theorem map_laurent {V W T : Model.{u}} (F F' : V ⟶ W) (J : W ⟶ T)
    (G : V ⟶ T) (ε : G.functor ≅ (F ≫ J).functor) (δ : F'.functor ≅ F.functor)
    (y : |parameterSSet G|) :
    map F F' J G ε δ (SSet.toTop.map (left₀ F J G ε) y) =
    SSet.toTop.map (left₀ F' J (F' ≫ J) (Iso.refl _))
      (mapParameter (CommonReferenceProduct.reanchor (laurentIso F F' J G ε δ)) y) := by
  exact ConcreteCategory.congr_hom (CutOpenMap.firstMap_left F J G F' J (F' ≫ J)
    ε (Iso.refl _) (TopCat.ofHom (mapParameter (CommonReferenceProduct.reanchor δ)))
    (TopCat.ofHom (mapParameter (CommonReferenceProduct.reanchor
      (laurentIso F F' J G ε δ)))) (attachment_square F F' J G ε δ)) y
end CoefficientBassPolynomialSheetNormalization

namespace CoefficientBassRaw1PolynomialPairCone
/-- The original correction leaves the prescribed whole Laurent side unchanged. -/
theorem corrected_left {R : CommRingCat.{u}} (P : Over (Spec R))
    (β : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c) (r : I) :
    corrected P β p q (r, 0) = chartSquare P β p q (r, 0) :=
  (correctedSquare P β p q).left r
end CoefficientBassRaw1PolynomialPairCone

namespace CoefficientBassRaw1PolynomialPostcomp
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  {a b c d : Under R} (p : a ⟶ b) (q : b ⟶ c) (w : c ⟶ d)

/-- The plus action keeps the exact original Laurent summand and reference transport. -/
theorem plus_laurent
    (y : |parameterSSet (pair P p q ≫ CoefficientBassSeedTargetChartAttachment.Ja P (a := c))|) :
    plus P p q w
      (SSet.toTop.map (left₀ (pair P p q) (CoefficientBassSeedTargetChartAttachment.Ja P (a := c))
        (pair P p q ≫ CoefficientBassSeedTargetChartAttachment.Ja P (a := c)) (Iso.refl _)) y) =
    SSet.toTop.map (left₀ (reference P p q w) (CoefficientBassSeedTargetChartAttachment.Jb P (b
      := d))
      (reference P p q w ≫ CoefficientBassSeedTargetChartAttachment.Jb P (b := d)) (Iso.refl _))
      (mapParameter (CommonReferenceProduct.reanchor
        (CoefficientBassPolynomialSheetNormalization.laurentIso
          (pair P p q ≫ CoefficientBassSeedTargetChartAttachment.M P w) (reference P p q w)
          (CoefficientBassSeedTargetChartAttachment.Jb P (b := d))
          ((pair P p q ≫ CoefficientBassSeedTargetChartAttachment.Ja P (a := c)) ≫
      CoefficientBassSeedTargetChartAttachment.L P w)
          (CoefficientBassSeedTargetChartAttachment.targetAnchor P w (pair P p q)
            (pair P p q ≫ CoefficientBassSeedTargetChartAttachment.Ja P (a := c)) (Iso.refl _))
          (polynomialIso P p q w)))
        (mapParameter (postcompNode (CoefficientBassSeedTargetChartAttachment.L P w)) y)) := by
  have h := CoefficientBassPositiveTargetSingleSheet.firstMap_laurent P w (pair P p q)
    (pair P p q ≫ CoefficientBassSeedTargetChartAttachment.Ja P (a := c)) (Iso.refl _) y
  have hn := congrArg
    (CoefficientBassPolynomialSheetNormalization.map
      (pair P p q ≫ CoefficientBassSeedTargetChartAttachment.M P w) (reference P p q w)
      (CoefficientBassSeedTargetChartAttachment.Jb P (b := d))
      ((pair P p q ≫ CoefficientBassSeedTargetChartAttachment.Ja P (a := c)) ≫
      CoefficientBassSeedTargetChartAttachment.L P w)
      (CoefficientBassSeedTargetChartAttachment.targetAnchor P w (pair P p q)
        (pair P p q ≫ CoefficientBassSeedTargetChartAttachment.Ja P (a := c)) (Iso.refl _))
      (polynomialIso P p q w)) h
  exact hn.trans (CoefficientBassPolynomialSheetNormalization.map_laurent _ _ _ _ _ _ _)

/-- The minus action keeps the exact original Laurent summand and reference transport. -/
theorem minus_laurent
    (y : |parameterSSet (pair P p q ≫ CoefficientBassNegativeTargetChartAttachment.Ja P (a :=
      c))|) :
    minus P p q w
      (SSet.toTop.map (left₀ (pair P p q) (CoefficientBassNegativeTargetChartAttachment.Ja P (a
      := c))
        (pair P p q ≫ CoefficientBassNegativeTargetChartAttachment.Ja P (a := c)) (Iso.refl _)) y) =
    SSet.toTop.map (left₀ (reference P p q w) (CoefficientBassNegativeTargetChartAttachment.Jb
      P (b := d))
      (reference P p q w ≫ CoefficientBassNegativeTargetChartAttachment.Jb P (b := d)) (Iso.refl _))
      (mapParameter (CommonReferenceProduct.reanchor
        (CoefficientBassPolynomialSheetNormalization.laurentIso
          (pair P p q ≫ CoefficientBassNegativeTargetChartAttachment.M P w) (reference P p q w)
          (CoefficientBassNegativeTargetChartAttachment.Jb P (b := d))
          ((pair P p q ≫ CoefficientBassNegativeTargetChartAttachment.Ja P (a := c)) ≫
      CoefficientBassNegativeTargetChartAttachment.L P w)
          (CoefficientBassNegativeTargetChartAttachment.targetAnchor P w (pair P p q)
            (pair P p q ≫ CoefficientBassNegativeTargetChartAttachment.Ja P (a := c)) (Iso.refl _))
          (polynomialIso P p q w)))
        (mapParameter (postcompNode (CoefficientBassNegativeTargetChartAttachment.L P w)) y)) := by
  have h := CoefficientBassNegativeTargetSingleSheet.firstMap_laurent P w (pair P p q)
    (pair P p q ≫ CoefficientBassNegativeTargetChartAttachment.Ja P (a := c)) (Iso.refl _) y
  have hn := congrArg
    (CoefficientBassPolynomialSheetNormalization.map
      (pair P p q ≫ CoefficientBassNegativeTargetChartAttachment.M P w) (reference P p q w)
      (CoefficientBassNegativeTargetChartAttachment.Jb P (b := d))
      ((pair P p q ≫ CoefficientBassNegativeTargetChartAttachment.Ja P (a := c)) ≫
      CoefficientBassNegativeTargetChartAttachment.L P w)
      (CoefficientBassNegativeTargetChartAttachment.targetAnchor P w (pair P p q)
        (pair P p q ≫ CoefficientBassNegativeTargetChartAttachment.Ja P (a := c)) (Iso.refl _))
      (polynomialIso P p q w)) h
  exact hn.trans (CoefficientBassPolynomialSheetNormalization.map_laurent _ _ _ _ _ _ _)

end CoefficientBassRaw1PolynomialPostcomp
end Quillen.PerfectComplexes
