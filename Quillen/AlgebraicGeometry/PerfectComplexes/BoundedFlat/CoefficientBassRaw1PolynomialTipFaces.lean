/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialPostcompCells
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialInputPlacement

/-! The original polynomial cap maps retain the same unreduced terminal tip. -/
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
/-- The first-sheet normalization keeps its literal terminal summand. -/
theorem map_tip {V W T : Model.{u}} (F F' : V ⟶ W) (J : W ⟶ T)
    (G : V ⟶ T) (ε : G.functor ≅ (F ≫ J).functor) (δ : F'.functor ≅ F.functor)
    (y : |tipSSet.{u}|) :
    map F F' J G ε δ (SSet.toTop.map (right₀ F J G ε) y) =
    SSet.toTop.map (right₀ F' J (F' ≫ J) (Iso.refl _)) y := by
  exact ConcreteCategory.congr_hom (CutOpenMap.firstMap_right F J G F' J (F' ≫ J)
    ε (Iso.refl _) (TopCat.ofHom (mapParameter (CommonReferenceProduct.reanchor δ)))
    (TopCat.ofHom (mapParameter (CommonReferenceProduct.reanchor
      (laurentIso F F' J G ε δ)))) (attachment_square F F' J G ε δ)) y
end CoefficientBassPolynomialSheetNormalization

namespace CoefficientBassPositiveTargetSingleSheet
/-- The actual chart action preserves its first unreduced tip. -/
theorem firstMap_tip {R : CommRingCat.{u}} (P : Over (Spec R))
    {a b : Under R} (f : a ⟶ b) {V : Model.{u+1}}
    (D : V ⟶ modelOf (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a))))
    (G : V ⟶ modelOf (boundedFlatPerfectWaldhausen
      (space (op P, (laurentUnderFunctor R).obj a))))
    (ε : G.functor ≅ (D ≫ CoefficientBassSeedTargetChartAttachment.Ja P (a := a)).functor)
    (y : |tipSSet.{u+1}|) :
    firstMap P f D G ε
      (SSet.toTop.map (right₀ D (CoefficientBassSeedTargetChartAttachment.Ja P (a := a)) G ε) y) =
    tip P f D G ε false := by
  have h := ContinuousMap.congr_fun (DoubleCylinder.homotopyDesc_right
    (SSet.toTop.map (attaching D (CoefficientBassSeedTargetChartAttachment.Ja P (a := a)) G ε))
    (SSet.toTop.map (erase D))
    (first_isPushout D (CoefficientBassSeedTargetChartAttachment.Ja P (a := a)) G ε)
    (laurentMap P f D G ε) (ContinuousMap.const _ (tip P f D G ε false))
    (nullTrack P f D G ε false)) y
  exact (congrArg (firstMap P f D G ε)
    (FourEdgeTree.SetDescent.eval_realized_right
      (attaching D (CoefficientBassSeedTargetChartAttachment.Ja P (a := a)) G ε) (erase D)
      y)).trans h
end CoefficientBassPositiveTargetSingleSheet

namespace CoefficientBassNegativeTargetSingleSheet
/-- The actual chart action preserves its first unreduced tip. -/
theorem firstMap_tip {R : CommRingCat.{u}} (P : Over (Spec R))
    {a b : Under R} (f : a ⟶ b) {V : Model.{u+1}}
    (D : V ⟶ modelOf (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a))))
    (G : V ⟶ modelOf (boundedFlatPerfectWaldhausen
      (space (op P, (laurentUnderFunctor R).obj a))))
    (ε : G.functor ≅ (D ≫ CoefficientBassNegativeTargetChartAttachment.Ja P (a := a)).functor)
    (y : |tipSSet.{u+1}|) :
    firstMap P f D G ε
      (SSet.toTop.map (right₀ D (CoefficientBassNegativeTargetChartAttachment.Ja P (a := a)) G
      ε) y) =
    tip P f D G ε false := by
  have h := ContinuousMap.congr_fun (DoubleCylinder.homotopyDesc_right
    (SSet.toTop.map (attaching D (CoefficientBassNegativeTargetChartAttachment.Ja P (a := a)) G ε))
    (SSet.toTop.map (erase D))
    (first_isPushout D (CoefficientBassNegativeTargetChartAttachment.Ja P (a := a)) G ε)
    (laurentMap P f D G ε) (ContinuousMap.const _ (tip P f D G ε false))
    (nullTrack P f D G ε false)) y
  exact (congrArg (firstMap P f D G ε)
    (FourEdgeTree.SetDescent.eval_realized_right
      (attaching D (CoefficientBassNegativeTargetChartAttachment.Ja P (a := a)) G ε) (erase D)
      y)).trans h
end CoefficientBassNegativeTargetSingleSheet

namespace CoefficientBassRaw1PolynomialPostcomp
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  {a b c d : Under R} (p : a ⟶ b) (q : b ⟶ c) (w : c ⟶ d)

/-- The common polynomial triple sheet has its original unreduced tip. -/
def tip (β : polynomialUnderFunctor R ⟶ laurentUnderFunctor R) : carrier P p q w β :=
  SSet.toTop.map (right₀ (reference P p q w)
    (BassMWholeNerve.coefficientModel P (β.app d))
    (reference P p q w ≫ BassMWholeNerve.coefficientModel P (β.app d)) (Iso.refl _))
    (default : |tipSSet.{u+1}|)

/-- The actual plus action keeps the triple sheet's terminal point. -/
theorem plus_tip :
    plus P p q w (CoefficientBassRaw1PolynomialPairCone.tip P (underToLaurent R) p q) =
    tip P p q w (underToLaurent R) := by
  have h := CoefficientBassPositiveTargetSingleSheet.firstMap_tip P w (pair P p q)
    (pair P p q ≫ CoefficientBassSeedTargetChartAttachment.Ja P (a := c)) (Iso.refl _)
    (default : |tipSSet.{u+1}|)
  have hn := congrArg
    (CoefficientBassPolynomialSheetNormalization.map
      (pair P p q ≫ CoefficientBassSeedTargetChartAttachment.M P w) (reference P p q w)
      (CoefficientBassSeedTargetChartAttachment.Jb P (b := d))
      ((pair P p q ≫ CoefficientBassSeedTargetChartAttachment.Ja P (a := c)) ≫
      CoefficientBassSeedTargetChartAttachment.L P w)
      (CoefficientBassSeedTargetChartAttachment.targetAnchor P w (pair P p q)
        (pair P p q ≫ CoefficientBassSeedTargetChartAttachment.Ja P (a := c)) (Iso.refl _))
      (polynomialIso P p q w)) h
  exact hn.trans (CoefficientBassPolynomialSheetNormalization.map_tip _ _ _ _ _ _ _)

/-- The whole top face of the unchanged corrected plus cap is the same tip. -/
theorem plus_cap_top (r : I) :
    plus P p q w (CoefficientBassRaw1PolynomialPairCone.corrected
      P (underToLaurent R) p q (r, 1)) = tip P p q w (underToLaurent R) :=
  (congrArg (plus P p q w)
    ((CoefficientBassRaw1PolynomialPairCone.correctedSquare P (underToLaurent R) p q).right
      r)).trans
      (plus_tip P p q w)

/-- The actual minus action keeps the triple sheet's terminal point. -/
theorem minus_tip :
    minus P p q w (CoefficientBassRaw1PolynomialPairCone.tip P (underToLaurentInvert R) p q) =
    tip P p q w (underToLaurentInvert R) := by
  have h := CoefficientBassNegativeTargetSingleSheet.firstMap_tip P w (pair P p q)
    (pair P p q ≫ CoefficientBassNegativeTargetChartAttachment.Ja P (a := c)) (Iso.refl _)
    (default : |tipSSet.{u+1}|)
  have hn := congrArg
    (CoefficientBassPolynomialSheetNormalization.map
      (pair P p q ≫ CoefficientBassNegativeTargetChartAttachment.M P w) (reference P p q w)
      (CoefficientBassNegativeTargetChartAttachment.Jb P (b := d))
      ((pair P p q ≫ CoefficientBassNegativeTargetChartAttachment.Ja P (a := c)) ≫
      CoefficientBassNegativeTargetChartAttachment.L P w)
      (CoefficientBassNegativeTargetChartAttachment.targetAnchor P w (pair P p q)
        (pair P p q ≫ CoefficientBassNegativeTargetChartAttachment.Ja P (a := c)) (Iso.refl _))
      (polynomialIso P p q w)) h
  exact hn.trans (CoefficientBassPolynomialSheetNormalization.map_tip _ _ _ _ _ _ _)

/-- The whole top face of the unchanged corrected minus cap is the same tip. -/
theorem minus_cap_top (r : I) :
    minus P p q w (CoefficientBassRaw1PolynomialPairCone.corrected
      P (underToLaurentInvert R) p q (r, 1)) = tip P p q w (underToLaurentInvert R) :=
  (congrArg (minus P p q w)
    ((CoefficientBassRaw1PolynomialPairCone.correctedSquare P (underToLaurentInvert R) p
      q).right r)).trans
      (minus_tip P p q w)

end CoefficientBassRaw1PolynomialPostcomp
namespace CoefficientBassRaw1PolynomialInputCap
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  (β : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  {a b c d : Under R} (f : a ⟶ b) (p : b ⟶ c) (q : c ⟶ d)
local notation "A" => CoefficientBassRaw1ChartCompositionProduct.polynomialInput P f
local notation "F" => CoefficientBassRaw1PolynomialPausedChart.polynomialReference P p q
local notation "J" => BassMWholeNerve.coefficientModel P (β.app d)
local notation "G" => CoefficientBassRaw1PolynomialPausedChart.sheetReference P β p q

/-- The whole top of the actual two-half input cap is the same fixed triple tip. -/
theorem placedFamily_top (r : I) : placedFamily P β f p q (r, 1) =
    CoefficientBassRaw1PolynomialPostcomp.tip P f p q β := by
  have h₀ : family P β f p q (r, 1) = last P β f p q (r, 1) :=
    ((firstSwap P β f p q).trans (lastSwap P β f p q)).apply_one r
  have h₁ := congrArg (precomp P β f p q)
    ((CoefficientBassRaw1PolynomialPairCone.correctedSquare P β p q).right r)
  have h₂ := ConcreteCategory.congr_hom
    (CutOpenPrecomp.firstMap_right A F J G (Iso.refl _)) (default : |tipSSet.{u+1}|)
  have h := congrArg (place P β f p q) (h₀.trans (h₁.trans h₂))
  exact h.trans (CoefficientBassPolynomialSheetNormalization.map_tip _ _ _ _ _ _ _)
end CoefficientBassRaw1PolynomialInputCap
end Quillen.PerfectComplexes
