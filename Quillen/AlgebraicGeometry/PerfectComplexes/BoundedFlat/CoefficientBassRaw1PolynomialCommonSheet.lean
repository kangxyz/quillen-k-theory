/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialRectangle
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialInputPlacement

/-! The three original polynomial cap sheets share the fixed full polynomial reference. -/
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
namespace Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialCommonSheet
open CommonReferenceNerve CommonReferenceNerve.CutOpenCarrier
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  (α β : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  {a b : Under R} (f : a ⟶ b)

/-- The original first triple supplies the fixed genuine polynomial reference. -/
abbrev reference := CoefficientBassRaw1PolynomialReference.polynomialReference P α f
/-- The coefficient model of the chart `β` at the Laurent coefficient object over `b`. -/
abbrev chart := BassMWholeNerve.coefficientModel P (β.app ((laurentUnderFunctor R).obj b))
/-- The first-sheet realization of the fixed polynomial reference with its identity anchor. -/
abbrev carrier := |firstSimplicial (reference P α f) (chart P β (b := b))
  (reference P α f ≫ chart P β (b := b)) (Iso.refl _)|

/-- The middle original triple is reanchored with its complete rectangle reference. -/
def middleMap : C(CoefficientBassRaw1PolynomialPostcomp.carrier P ((polynomialUnderCoefficient
      R).app a) ((polynomialUnderFunctor R).map f) (α.app b) β,
    carrier P α β f) :=
  CoefficientBassPolynomialSheetNormalization.map
    (CoefficientBassRaw1PolynomialPostcomp.reference P ((polynomialUnderCoefficient R).app a)
      ((polynomialUnderFunctor R).map f) (α.app b)) (reference P α f)
    (chart P β (b := b))
    ((CoefficientBassRaw1PolynomialPostcomp.reference P ((polynomialUnderCoefficient R).app a)
      ((polynomialUnderFunctor R).map f) (α.app b)) ≫ chart P β (b := b))
    (Iso.refl _) (CoefficientBassRaw1PolynomialRectangle.middleAnchor P α f)

/-- Full reference normalization preserves every native value of the middle cap. -/
theorem middleMap_native (n : ℕ)
    (z : CoefficientBassRaw1PolynomialPostcomp.carrier P ((polynomialUnderCoefficient R).app a)
      ((polynomialUnderFunctor R).map f) (α.app b) β)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a)))).space n) :
    CoefficientBassRaw1PolynomialPostcomp.evaluate P
      ((polynomialUnderCoefficient R).app a) (α.app a) ((laurentUnderFunctor R).map f) β n
      (middleMap P α β f z) x =
    CoefficientBassRaw1PolynomialPostcomp.evaluate P ((polynomialUnderCoefficient R).app a)
      ((polynomialUnderFunctor R).map f) (α.app b) β n z x :=
  CoefficientBassPolynomialSheetNormalization.map_native
    (CoefficientBassRaw1PolynomialPostcomp.reference P ((polynomialUnderCoefficient R).app a)
      ((polynomialUnderFunctor R).map f) (α.app b)) (reference P α f)
    (chart P β (b := b))
    ((CoefficientBassRaw1PolynomialPostcomp.reference P ((polynomialUnderCoefficient R).app a)
      ((polynomialUnderFunctor R).map f) (α.app b)) ≫ chart P β (b := b))
    (Iso.refl _) (CoefficientBassRaw1PolynomialRectangle.middleAnchor P α f) n z x

/-- The last original triple is reanchored with its complete rectangle reference. -/
def lastMap : C(CoefficientBassRaw1PolynomialPostcomp.carrier P f ((polynomialUnderCoefficient
      R).app b) (α.app b) β,
    carrier P α β f) :=
  CoefficientBassPolynomialSheetNormalization.map
    (CoefficientBassRaw1PolynomialPostcomp.reference P f ((polynomialUnderCoefficient R).app b)
      (α.app b)) (reference P α f)
    (chart P β (b := b))
    ((CoefficientBassRaw1PolynomialPostcomp.reference P f ((polynomialUnderCoefficient R).app
      b) (α.app b)) ≫ chart P β (b := b))
    (Iso.refl _) (CoefficientBassRaw1PolynomialRectangle.lastAnchor P α f)

/-- Full reference normalization preserves every native value of the last cap. -/
theorem lastMap_native (n : ℕ)
    (z : CoefficientBassRaw1PolynomialPostcomp.carrier P f ((polynomialUnderCoefficient R).app
      b) (α.app b) β)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a)))).space n) :
    CoefficientBassRaw1PolynomialPostcomp.evaluate P
      ((polynomialUnderCoefficient R).app a) (α.app a) ((laurentUnderFunctor R).map f) β n
      (lastMap P α β f z) x =
    CoefficientBassRaw1PolynomialPostcomp.evaluate P f ((polynomialUnderCoefficient R).app b)
      (α.app b) β n z x :=
  CoefficientBassPolynomialSheetNormalization.map_native
    (CoefficientBassRaw1PolynomialPostcomp.reference P f ((polynomialUnderCoefficient R).app b)
      (α.app b)) (reference P α f)
    (chart P β (b := b))
    ((CoefficientBassRaw1PolynomialPostcomp.reference P f ((polynomialUnderCoefficient R).app
      b) (α.app b)) ≫ chart P β (b := b))
    (Iso.refl _) (CoefficientBassRaw1PolynomialRectangle.lastAnchor P α f) n z x

end Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialCommonSheet
