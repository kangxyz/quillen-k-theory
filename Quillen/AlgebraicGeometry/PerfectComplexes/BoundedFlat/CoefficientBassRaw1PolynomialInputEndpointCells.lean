/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialInputPolynomialEndpoint
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialInputFirstEndpointRow
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialDirectPathCells

/-! The literal cylinder cell of the radial and input endpoint comparison. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.NativePathCells
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes
open CommonReferenceNerve CommonReferenceNerve.CutOpenCarrier
namespace CoefficientBassRaw1PolynomialInputEndpointCells
private theorem precomp_cylinder {U V W T : Model.{u}} (A : U ⟶ V)
    (F : V ⟶ W) (J : W ⟶ T) (G : V ⟶ T) (ε : G.functor ≅ (F ≫ J).functor)
    (y : |parameterSSet F|) (t : I) :
    CutOpenPrecomp.firstMap A F J G ε
      (DoubleCylinder.realizedCylinder (attaching F J G ε) (erase F) (y, ULift.up t)) =
    DoubleCylinder.realizedCylinder
      (attaching (A ≫ F) J (A ≫ G) (CutOpenPrecomp.anchor A F J G ε)) (erase (A ≫ F))
      (mapParameter (precompNode A) y, ULift.up t) :=
  DoubleCylinder.map_cylinder_apply (first_isPushout F J G ε)
    (first_isPushout (A ≫ F) J (A ≫ G) (CutOpenPrecomp.anchor A F J G ε))
    (CutOpenPrecomp.parameterMap A F) (CutOpenPrecomp.parameterMap A G) (𝟙 _)
    (CutOpenPrecomp.attachment_square A F J G ε)
    (CutOpenMap.erase_square F (A ≫ F) (CutOpenPrecomp.parameterMap A F)) y (ULift.up t)

variable {R : CommRingCat.{u}} (P : Over (Spec R))
  (β : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  {a b c d : Under R} (p : a ⟶ b) (q : b ⟶ c) (w : c ⟶ d)

/-- Both original endpoint words have the identical whole polynomial cylinder cell. -/
theorem placed_cylinder (s : I) :
    CoefficientBassRaw1PolynomialInputCap.place P β p q w
      (CoefficientBassRaw1PolynomialInputCap.precomp P β p q w
        (CoefficientBassRaw1PolynomialPairCone.cylinder P β q w
          (CoefficientBassRaw1PolynomialSourceAttachment.polynomialPausedPath P q w 0, s))) =
    CoefficientBassRaw1PolynomialRadialCaps.rightMap P β p q w
      (CoefficientBassRaw1PolynomialPairCone.thirdPath P β p (q ≫ w) s) := by
  let A := CoefficientBassRaw1ChartCompositionProduct.polynomialInput P p
  let F := CoefficientBassRaw1PolynomialPausedChart.polynomialReference P q w
  let J := BassMWholeNerve.coefficientModel P (β.app d)
  let G := CoefficientBassRaw1PolynomialPausedChart.sheetReference P β q w
  let ε := CutOpenPrecomp.anchor A F J G (Iso.refl _)
  have hp := precomp_cylinder A F J G (Iso.refl _)
    (CoefficientBassRaw1PolynomialSourceAttachment.polynomialPausedPath P q w 0) s
  have h := congrArg (CoefficientBassRaw1PolynomialInputCap.place P β p q w) hp
  have hm := CoefficientBassPolynomialSheetNormalization.map_cylinder (A ≫ F)
    (CoefficientBassRaw1PolynomialPostcomp.reference P p q w) J (A ≫ G) ε
    (CoefficientBassRaw1PolynomialInputCap.polynomialIso P p q w)
    (mapParameter (precompNode A)
      (CoefficientBassRaw1PolynomialSourceAttachment.polynomialPausedPath P q w 0)) s
  have hr := CoefficientBassPolynomialSheetNormalization.map_cylinder
    (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P p (q ≫ w))
    (CoefficientBassRaw1PolynomialPostcomp.reference P p q w) J
    (CoefficientBassRaw1PolynomialPausedChart.sheetReference P β p (q ≫ w)) (Iso.refl _)
    (CoefficientBassRaw1PolynomialRadialCaps.rightPolynomialIso P p q w)
    (CoefficientBassRaw1PolynomialSourceAttachment.polynomialPausedPath P p (q ≫ w) 1) s
  have he := congrArg (fun y ↦ DoubleCylinder.realizedCylinder
    (attaching (CoefficientBassRaw1PolynomialPostcomp.reference P p q w) J
      ((CoefficientBassRaw1PolynomialPostcomp.reference P p q w) ≫ J) (Iso.refl _))
    (erase (CoefficientBassRaw1PolynomialPostcomp.reference P p q w)) (y, ULift.up s))
    (CoefficientBassRaw1PolynomialInputPolynomialEndpoint.polynomial_parameter P p q w)
  exact (h.trans hm).trans (he.trans hr.symm)

/-- The placed input cap preserves its literal first outer-height half. -/
theorem placed_lower (r t : I) :
    CoefficientBassRaw1PolynomialInputCap.placedFamily P β p q w (r, lower t) =
      CoefficientBassRaw1PolynomialInputCap.place P β p q w
        (CoefficientBassRaw1PolynomialInputCap.first P β p q w (r, t)) :=
  congrArg (CoefficientBassRaw1PolynomialInputCap.place P β p q w)
    (ScalarRectangle.homotopy_lower
      (CoefficientBassRaw1PolynomialInputCap.firstSwap P β p q w)
      (CoefficientBassRaw1PolynomialInputCap.lastSwap P β p q w) t r)

/-- The placed input cap preserves its literal second outer-height half. -/
theorem placed_upper (r t : I) :
    CoefficientBassRaw1PolynomialInputCap.placedFamily P β p q w (r, upper t) =
      CoefficientBassRaw1PolynomialInputCap.place P β p q w
        (CoefficientBassRaw1PolynomialInputCap.last P β p q w (r, t)) :=
  congrArg (CoefficientBassRaw1PolynomialInputCap.place P β p q w)
    (ScalarRectangle.homotopy_upper
      (CoefficientBassRaw1PolynomialInputCap.firstSwap P β p q w)
      (CoefficientBassRaw1PolynomialInputCap.lastSwap P β p q w) t r)

/-- The first placed endpoint cell is the original first radial path, at the same clock. -/
theorem placed_first_path (t : I) :
    CoefficientBassRaw1PolynomialInputCap.place P β p q w
      (CoefficientBassRaw1PolynomialInputCap.first P β p q w (0, t)) =
    CoefficientBassRaw1PolynomialRadialCaps.rightMap P β p q w
      (CoefficientBassRaw1PolynomialPairCone.firstPath P β p (q ≫ w) t) := by
  have h := CoefficientBassRaw1PolynomialInputFirstEndpointRow.placed_first P β p q w t
  have hr := congrArg (CoefficientBassRaw1PolynomialRadialCaps.rightMap P β p q w)
    (CoefficientBassRaw1PolynomialPairCone.firstPath_row P β p (q ≫ w) t)
  have hn := congrArg (fun ns ↦ CoefficientBassRaw1PolynomialRadialCaps.rightMap P β p q w
    (CoefficientBassRaw1PolynomialPairCone.laurent P β p (q ≫ w)
      (parameter (CoefficientBassRaw1PolynomialPausedChart.sheetReference P β p (q ≫ w)) ns
        (NativeSquareFiveSimplex.parameter t))))
    (funext (CoefficientBassRaw1PolynomialPairEndpointReferences.first_nodes P β p (q ≫ w)))
  exact h.trans (hn.symm.trans hr.symm)

end CoefficientBassRaw1PolynomialInputEndpointCells
end Quillen.PerfectComplexes
