/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialInputEndpointCells
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialInputSecondEndpointRow

/-! The complete right-radial and input-cap endpoint word. -/
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
namespace Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialInputRadialSeam
open CommonReferenceNerve CoefficientBassRaw1PolynomialInputEndpointCells
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  (β : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  {a b c d : Under R} (p : a ⟶ b) (q : b ⟶ c) (w : c ⟶ d)

private theorem last_zero_lower (t : I) :
    CoefficientBassRaw1PolynomialInputCap.last P β p q w (0, lower t) =
    CoefficientBassRaw1PolynomialInputCap.precomp P β p q w
      (CoefficientBassRaw1PolynomialPairCone.chartSquare P β q w (0, t)) := by
  have h := CoefficientBassRaw1PolynomialPairCone.corrected_zero P β q w (lower t)
  have ht := ScalarRectangle.homotopy_lower
    (CoefficientBassRaw1PolynomialPairCone.firstSwap P β q w)
    (CoefficientBassRaw1PolynomialPairCone.lastSwap P β q w) t 0
  exact congrArg (CoefficientBassRaw1PolynomialInputCap.precomp P β p q w) (h.trans ht)

private theorem last_zero_upper (t : I) :
    CoefficientBassRaw1PolynomialInputCap.last P β p q w (0, upper t) =
    CoefficientBassRaw1PolynomialInputCap.precomp P β p q w
      (CoefficientBassRaw1PolynomialPairCone.cylinder P β q w
        (CoefficientBassRaw1PolynomialSourceAttachment.polynomialPausedPath P q w 0, t)) := by
  have h := CoefficientBassRaw1PolynomialPairCone.corrected_zero P β q w (upper t)
  have ht := ScalarRectangle.homotopy_upper
    (CoefficientBassRaw1PolynomialPairCone.firstSwap P β q w)
    (CoefficientBassRaw1PolynomialPairCone.lastSwap P β q w) t 0
  exact congrArg (CoefficientBassRaw1PolynomialInputCap.precomp P β p q w) (h.trans ht)

/-- The full original input endpoint equals the whole terminal radial word. -/
theorem input_zero (s : I) :
    CoefficientBassRaw1PolynomialInputCap.placedFamily P β p q w (0, s) =
    CoefficientBassRaw1PolynomialRadialCaps.right P β p q w (1, s) := by
  obtain ⟨t, rfl⟩ | ⟨t, rfl⟩ := cover s
  · have hl := (placed_lower P β p q w 0 t).trans (placed_first_path P β p q w t)
    have hr := congrArg (CoefficientBassRaw1PolynomialRadialCaps.rightMap P β p q w)
      (CoefficientBassRaw1PolynomialPairCone.corrected_one P β p (q ≫ w) (lower t))
    rw [path_lower] at hr
    exact hl.trans hr.symm
  · obtain ⟨v, rfl⟩ | ⟨v, rfl⟩ := cover t
    · have hl := (placed_upper P β p q w 0 (lower v)).trans
        (congrArg (CoefficientBassRaw1PolynomialInputCap.place P β p q w)
          (last_zero_lower P β p q w v))
      have hc := CoefficientBassRaw1PolynomialInputSecondEndpointRow.placed_second P β p q w v
      have hr := congrArg (CoefficientBassRaw1PolynomialRadialCaps.rightMap P β p q w)
        (CoefficientBassRaw1PolynomialPairCone.corrected_one P β p (q ≫ w) (upper (lower v)))
      rw [path_upper, path_lower] at hr
      exact (hl.trans hc).trans hr.symm
    · have hl := (placed_upper P β p q w 0 (upper v)).trans
        (congrArg (CoefficientBassRaw1PolynomialInputCap.place P β p q w)
          (last_zero_upper P β p q w v))
      have hr := congrArg (CoefficientBassRaw1PolynomialRadialCaps.rightMap P β p q w)
        (CoefficientBassRaw1PolynomialPairCone.corrected_one P β p (q ≫ w) (upper (upper v)))
      rw [path_upper, path_upper] at hr
      exact (hl.trans (placed_cylinder P β p q w v)).trans hr.symm

end Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialInputRadialSeam
