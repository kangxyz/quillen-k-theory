/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1ChartCompositionCells
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialPairCorrected
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassCutOpenPrecompMap

/-! The two literal halves of the original cone-composition cap evaluated on a Bass map. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialInputCap
open CommonReferenceNerve CommonReferenceNerve.CutOpenCarrier
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  (β : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  {a b c d : Under R} (f : a ⟶ b) (p : b ⟶ c) (q : c ⟶ d)
local notation "A" => CoefficientBassRaw1ChartCompositionProduct.polynomialInput P f
local notation "F" => CoefficientBassRaw1PolynomialPausedChart.polynomialReference P p q
local notation "J" => BassMWholeNerve.coefficientModel P (β.app d)
local notation "G" => CoefficientBassRaw1PolynomialPausedChart.sheetReference P β p q
local notation "ε" => CutOpenPrecomp.anchor A F J G (Iso.refl _)

/-- Source precomposition retains the original first sheet and its complete anchor. -/
abbrev carrier := |firstSimplicial (A ≫ F) J (A ≫ G) ε|

/-- The Laurent summand remains available for every genuine polynomial input. -/
def laurent : C(|parameterSSet (A ≫ G)|, carrier P β f p q) :=
  (SSet.toTop.map (left₀ (A ≫ F) J (A ≫ G) ε)).hom

/-- The literal first-sheet map preserves the old corrected cap. -/
def precomp : C(CoefficientBassRaw1PolynomialPairCone.carrier P β p q,
    carrier P β f p q) := (CutOpenPrecomp.firstMap A F J G (Iso.refl _)).hom

/-- The chart-square half is placed by its complete terminal reference isomorphism. -/
def first : C(I × I, carrier P β f p q) :=
  (laurent P β f p q).comp
    ((mapParameter (CommonReferenceProduct.reanchor
      (CoefficientBassRaw1ChartCompositionProduct.midpointIso P β f p q).symm)).comp
      (CoefficientBassRaw1ChartCompositionProduct.family P β f p q))

/-- The cylinder half is the unchanged original corrected pair cap under source precomposition. -/
def last : C(I × I, carrier P β f p q) :=
  (precomp P β f p q).comp (CoefficientBassRaw1PolynomialPairCone.corrected P β p q)

/-- Inverse reference transport cancels on the complete source-precomposed nerve. -/
theorem midpoint_cancel (y : |parameterSSet G|) :
    mapParameter (CommonReferenceProduct.reanchor
      (CoefficientBassRaw1ChartCompositionProduct.midpointIso P β f p q).symm)
      (mapParameter (fun N ↦ CommonReferenceProduct.reanchor
        (CoefficientBassRaw1ChartCompositionProduct.midpointIso P β f p q)
        (precompNode A N)) y) = mapParameter (precompNode A) y := by
  obtain ⟨k, N, z, rfl⟩ := exists_parameter G y
  rw [mapParameter_parameter, mapParameter_parameter, mapParameter_parameter]
  apply congrArg (fun M ↦ parameter (A ≫ G) M z)
  funext i
  apply Sigma.ext
  · rfl
  apply heq_of_eq
  simp only [CommonReferenceProduct.reanchor, Iso.symm_self_id_assoc]

/-- The actual original cap halves agree on their full midpoint before native evaluation. -/
theorem seam (r : I) : first P β f p q (r, 1) = last P β f p q (r, 0) := by
  dsimp only [first, last, ContinuousMap.comp_apply]
  rw [CoefficientBassRaw1ChartCompositionProduct.family_terminal, midpoint_cancel]
  have h := (CoefficientBassRaw1PolynomialPairCone.correctedSquare P β p q).left r
  change CoefficientBassRaw1PolynomialPairCone.corrected P β p q (r, 0) =
    CoefficientBassRaw1PolynomialPairCone.chartSquare P β p q (r, 0) at h
  rw [h]
  exact (ConcreteCategory.congr_hom (CutOpenPrecomp.firstMap_left A F J G (Iso.refl _))
    (CoefficientBassRaw1PolynomialPausedChart.sheetFamily P β p q (r, 0))).symm

/-- The three full edge maps are retained when forming the original outer-height split. -/
def start : C(I, carrier P β f p q) := ⟨fun r ↦ first P β f p q (r, 0), by fun_prop⟩
/-- The terminal edge of the chart-square half, where the two input-cap halves meet. -/
def middle : C(I, carrier P β f p q) := ⟨fun r ↦ first P β f p q (r, 1), by fun_prop⟩
/-- The terminal edge of the source-precomposed corrected pair cap. -/
def finish : C(I, carrier P β f p q) := ⟨fun r ↦ last P β f p q (r, 1), by fun_prop⟩

/-- The homotopy from the start edge to the middle edge given by the chart-square half. -/
def firstSwap : (start P β f p q).Homotopy (middle P β f p q) where
  toFun z := first P β f p q (z.2, z.1)
  continuous_toFun := by fun_prop
  map_zero_left _ := rfl
  map_one_left _ := rfl

/-- The homotopy from the middle edge to the finish edge given by the precomposed pair cap. -/
def lastSwap : (middle P β f p q).Homotopy (finish P β f p q) where
  toFun z := last P β f p q (z.2, z.1)
  continuous_toFun := by fun_prop
  map_zero_left r := (seam P β f p q r).symm
  map_one_left _ := rfl

/-- This cap retains exactly the Bass-map outer-height half split and the old pair correction. -/
def family : C(I × I, carrier P β f p q) :=
  ⟨fun z ↦ ((firstSwap P β f p q).trans (lastSwap P β f p q)) (z.2, z.1), by fun_prop⟩

end Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialInputCap
