/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialPairCone
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveFourEdgeEvaluation

/-! Exact whole attachment and tip laws of the original pair's single polynomial sheet. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Quillen.LoopPrespectrum
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialPairCone
open CommonReferenceNerve CommonReferenceNerve.CutOpenCarrier
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  (β : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)
local notation "F" => CoefficientBassRaw1PolynomialPausedChart.polynomialReference P p q
local notation "J" => BassMWholeNerve.coefficientModel P (β.app c)
local notation "G" => CoefficientBassRaw1PolynomialPausedChart.sheetReference P β p q

/-- The Laurent parameter inclusion into the first polynomial-pair sheet. -/
def laurent : C(|parameterSSet G|, carrier P β p q) :=
  (SSet.toTop.map (left₀ F J G (Iso.refl _))).hom

/-- The polynomial-pair sheet cylinder with its original interval coordinate. -/
def cylinder : C(|parameterSSet F| × I, carrier P β p q) where
  toFun z := DoubleCylinder.realizedCylinder (attaching F J G (Iso.refl _)) (erase F)
    (z.1, ULift.up z.2)
  continuous_toFun :=
    (DoubleCylinder.realizedCylinder (attaching F J G (Iso.refl _)) (erase F)).hom.continuous.comp
      (by fun_prop)

/-- The terminal tip of the first polynomial-pair sheet. -/
def tip : carrier P β p q :=
  SSet.toTop.map (right₀ F J G (Iso.refl _)) (default : |tipSSet.{u+1}|)

/-- The attachment is a whole nerve equality at the unchanged zero height. -/
theorem cylinder_zero (y : |parameterSSet F|) : cylinder P β p q (y, 0) =
    laurent P β p q (SSet.toTop.map (attaching F J G (Iso.refl _)) y) := by
  have h := ConcreteCategory.congr_hom
    (DoubleCylinder.realized_isPushout (attaching F J G (Iso.refl _)) (erase F)).w (Sum.inl y)
  exact h.trans (FourEdgeTree.SetDescent.eval_realized_left _ _ _).symm

/-- The entire terminal edge is the single original unreduced tip. -/
theorem cylinder_one (y : |parameterSSet F|) : cylinder P β p q (y, 1) = tip P β p q := by
  have h := ConcreteCategory.congr_hom
    (DoubleCylinder.realized_isPushout (attaching F J G (Iso.refl _)) (erase F)).w (Sum.inr y)
  exact h.trans ((FourEdgeTree.SetDescent.eval_realized_right _ _ _).symm.trans
    (congrArg (SSet.toTop.map (right₀ F J G (Iso.refl _))) (Subsingleton.elim _ _)))

/-- The unchanged height evaluates in the original target chart cone. -/
theorem cylinder_native (n : ℕ) (y : |parameterSSet F|) (h : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a)))).space n) :
    evaluate P β p q n (cylinder P β p q (y, h)) x =
      Quillen.ReducedMappingCone.cylinder _ _ ((prespectrumMap J).map n)
        (h, pointwisePrespectrumFamily F n y x) :=
  nativeEval_cylinderMinus _ _ _ _ _ n y h x

end Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialPairCone
