/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialPostcompInputEndpoint
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialInputRadialSeam
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialPostcompRadialEndpoint
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialRadialDirectSeam
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialTipFaces

/-! The two actual split-triple cap routes, with every old half clock and shared full edge. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.NativePathCells
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialTripleRoutes
open CommonReferenceNerve
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  {a b c d : Under R} (p : a ⟶ b) (q : b ⟶ c) (w : c ⟶ d)

/-- The independent original outer chart sign. -/
def chartChoice (negative : Bool) : polynomialUnderFunctor R ⟶ laurentUnderFunctor R :=
  if negative then underToLaurentInvert R else underToLaurent R

/-- The actual postcomposed pair cap, for each original outer sign. -/
def postCap (negative : Bool) : C(I × I,
    CoefficientBassRaw1PolynomialPostcomp.carrier P p q w (chartChoice (R := R) negative)) := by
  cases negative
  · exact (CoefficientBassRaw1PolynomialPostcomp.plus P p q w).comp
      (CoefficientBassRaw1PolynomialPairCone.corrected P (underToLaurent R) p q)
  · exact (CoefficientBassRaw1PolynomialPostcomp.minus P p q w).comp
      (CoefficientBassRaw1PolynomialPairCone.corrected P (underToLaurentInvert R) p q)

/-- The left route uses the complete checked radial/postcomposition seam. -/
theorem left_join (negative : Bool) (s : I) :
    CoefficientBassRaw1PolynomialRadialCaps.left P (chartChoice negative) p q w (1, s) =
      postCap P p q w negative (0, s) := by
  cases negative
  · exact CoefficientBassRaw1PolynomialPostcompRadialEndpoint.plus_left_one P p q w s
  · exact CoefficientBassRaw1PolynomialPostcompRadialEndpoint.minus_left_one P p q w s

/-- The right route uses the complete checked radial/input seam. -/
theorem right_join (negative : Bool) (s : I) :
    CoefficientBassRaw1PolynomialRadialCaps.right P (chartChoice negative) p q w (1, s) =
      CoefficientBassRaw1PolynomialInputCap.placedFamily P (chartChoice negative) p q w (0, s) :=
  (CoefficientBassRaw1PolynomialInputRadialSeam.input_zero P (chartChoice negative) p q w s).symm

/-- Both original left pair comparisons retain their fixed half clocks. -/
def left (negative : Bool) := ScalarRectangle.concatFirst
  (CoefficientBassRaw1PolynomialRadialCaps.left P (chartChoice negative) p q w)
  (postCap P p q w negative) (left_join P p q w negative)

/-- Both original right pair comparisons retain their separate fixed half clocks. -/
def right (negative : Bool) := ScalarRectangle.concatFirst
  (CoefficientBassRaw1PolynomialRadialCaps.right P (chartChoice negative) p q w)
  (CoefficientBassRaw1PolynomialInputCap.placedFamily P (chartChoice negative) p q w)
  (right_join P p q w negative)

/-- Both routes start at the exact whole direct composite word. -/
theorem start (negative : Bool) (s : I) : left P p q w negative (0, s) =
    right P p q w negative (0, s) := by
  rw [left, right, ScalarRectangle.concatFirst_zero, ScalarRectangle.concatFirst_zero]
  cases negative
  · exact CoefficientBassRaw1PolynomialRadialDirectSeam.plus_radial_zero P p q w s
  · exact CoefficientBassRaw1PolynomialRadialDirectSeam.minus_radial_zero P p q w s

/-- The complete left radial cap retains the same unreduced tip. -/
theorem radial_left_top (β : polynomialUnderFunctor R ⟶ laurentUnderFunctor R) (r : I) :
    CoefficientBassRaw1PolynomialRadialCaps.left P β p q w (r, 1) =
      CoefficientBassRaw1PolynomialPostcomp.tip P p q w β := by
  have h := congrArg (CoefficientBassRaw1PolynomialRadialCaps.leftMap P β p q w)
    ((CoefficientBassRaw1PolynomialPairCone.correctedSquare P β (p ≫ q) w).right r)
  exact h.trans (CoefficientBassPolynomialSheetNormalization.map_tip _ _ _ _ _ _ _)

/-- The complete right radial cap retains the same unreduced tip. -/
theorem radial_right_top (β : polynomialUnderFunctor R ⟶ laurentUnderFunctor R) (r : I) :
    CoefficientBassRaw1PolynomialRadialCaps.right P β p q w (r, 1) =
      CoefficientBassRaw1PolynomialPostcomp.tip P p q w β := by
  have h := congrArg (CoefficientBassRaw1PolynomialRadialCaps.rightMap P β p q w)
    ((CoefficientBassRaw1PolynomialPairCone.correctedSquare P β p (q ≫ w)).right r)
  exact h.trans (CoefficientBassPolynomialSheetNormalization.map_tip _ _ _ _ _ _ _)

/-- The whole left route fixes the original tip at every route time. -/
theorem left_top (negative : Bool) (r : I) : left P p q w negative (r, 1) =
    CoefficientBassRaw1PolynomialPostcomp.tip P p q w (chartChoice negative) := by
  obtain ⟨t, rfl⟩ | ⟨t, rfl⟩ := cover r
  · exact (ScalarRectangle.concatFirst_lower _ _ _ t 1).trans
      (radial_left_top P p q w (chartChoice negative) t)
  · have h := ScalarRectangle.concatFirst_upper
      (CoefficientBassRaw1PolynomialRadialCaps.left P (chartChoice negative) p q w)
      (postCap P p q w negative) (left_join P p q w negative) t 1
    refine h.trans ?_
    cases negative
    · exact CoefficientBassRaw1PolynomialPostcomp.plus_cap_top P p q w t
    · exact CoefficientBassRaw1PolynomialPostcomp.minus_cap_top P p q w t

/-- The whole right route fixes that identical tip with its original half clocks. -/
theorem right_top (negative : Bool) (r : I) : right P p q w negative (r, 1) =
    CoefficientBassRaw1PolynomialPostcomp.tip P p q w (chartChoice negative) := by
  obtain ⟨t, rfl⟩ | ⟨t, rfl⟩ := cover r
  · exact (ScalarRectangle.concatFirst_lower _ _ _ t 1).trans
      (radial_right_top P p q w (chartChoice negative) t)
  · exact (ScalarRectangle.concatFirst_upper _ _ _ t 1).trans
      (CoefficientBassRaw1PolynomialInputCap.placedFamily_top P (chartChoice negative) p q w t)

/-- Both routes finish at the same complete original three-map composite word. -/
theorem finish (negative : Bool) (s : I) : left P p q w negative (1, s) =
    right P p q w negative (1, s) := by
  rw [left, right, ScalarRectangle.concatFirst_one, ScalarRectangle.concatFirst_one]
  cases negative
  · exact CoefficientBassRaw1PolynomialPostcompInputEndpoint.plus_endpoint P p q w s
  · exact CoefficientBassRaw1PolynomialPostcompInputEndpoint.minus_endpoint P p q w s

end Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialTripleRoutes
