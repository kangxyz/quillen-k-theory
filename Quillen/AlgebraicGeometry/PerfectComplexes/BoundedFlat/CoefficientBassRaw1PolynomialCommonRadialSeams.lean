/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialCommonRadialCaps
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPolynomialSheetNormalizationComposition

/-!
# Whole shared radial faces in the actual common polynomial sheet

The original corrected pair caps coincide at every composition time and every
height after their full polynomial-reference normalizations. The proof uses the
actual coefficient and chart naturality equations, independently for both charts.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u v
namespace Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialCommonRadialSeams
open CommonReferenceNerve CommonReferenceNerve.CutOpenCarrier
open CoefficientBassRaw1PolynomialCommonRadialCaps

private theorem equality_iso_heq {C : Type u} [Category.{v} C]
    (F M N : C) (h : F = M) (k : F = N) : HEq (eqToIso h) (eqToIso k) := by
  cases h
  cases k
  rfl

variable {R : CommRingCat.{u}} (P : Over (Spec R))
  (β : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)

/-- The entire original corrected pair cap in a specified full polynomial reference. -/
def pairInto {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)
    (F : CoefficientBassRaw1PolynomialSourceCylinder.model P a ⟶
      CoefficientBassRaw1PolynomialSourceCylinder.model P c)
    (η : F.functor ≅ (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P p q).functor) :
    C(I × I, |firstSimplicial F (BassMWholeNerve.coefficientModel P (β.app c))
      (F ≫ BassMWholeNerve.coefficientModel P (β.app c)) (Iso.refl _)|) :=
  (CoefficientBassPolynomialSheetNormalization.map
    (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P p q) F
    (BassMWholeNerve.coefficientModel P (β.app c))
    (CoefficientBassRaw1PolynomialPausedChart.sheetReference P β p q) (Iso.refl _) η).comp
      (CoefficientBassRaw1PolynomialPairCone.corrected P β p q)

/-- Actual pair equality transports the whole corrected cap, with its full reference. -/
theorem pairInto_congr {a b c : Under R} (p p' : a ⟶ b) (q q' : b ⟶ c)
    (hp : p = p') (hq : q = q')
    (F : CoefficientBassRaw1PolynomialSourceCylinder.model P a ⟶
      CoefficientBassRaw1PolynomialSourceCylinder.model P c)
    (η : F.functor ≅ (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P p q).functor)
    (θ : F.functor ≅ (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P p' q').functor)
    (hη : HEq η θ) : pairInto P β p q F η = pairInto P β p' q' F θ := by
  subst p'
  subst q'
  have hh := eq_of_heq hη
  subst θ
  rfl

variable (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  {a b : Under R} (f : a ⟶ b)

private theorem middle_anchor_equality : ∃ h,
    CoefficientBassRaw1PolynomialRectangle.middleAnchor P α f = eqToIso h := by
  exact ⟨_, BassReferenceMerge.smallIso_eqToIso _⟩

private theorem last_anchor_equality : ∃ h,
    CoefficientBassRaw1PolynomialRectangle.lastAnchor P α f = eqToIso h := by
  exact ⟨_, BassReferenceMerge.smallIso_eqToIso _⟩

/-- The first and middle right caps are the same entire original corrected radial face. -/
theorem first_right_eq_middle_right {R : CommRingCat.{u}} (P : Over (Spec R))
    (α β : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    {a b : Under R} (f : a ⟶ b) :
    firstRight P α β f = middleRight P α β f := by
  obtain ⟨hM, ehM⟩ := middle_anchor_equality P α f
  have hi : HEq
      (CoefficientBassRaw1PolynomialRadialCaps.rightPolynomialIso P
        ((polynomialUnderCoefficient R).app a) (α.app a) ((laurentUnderFunctor R).map f))
      (CoefficientBassRaw1PolynomialRectangle.middleAnchor P α f ≪≫
        CoefficientBassRaw1PolynomialRadialCaps.rightPolynomialIso P
          ((polynomialUnderCoefficient R).app a) ((polynomialUnderFunctor R).map f) (α.app b)) := by
    rw [ehM]
    dsimp only [CoefficientBassRaw1PolynomialRadialCaps.rightPolynomialIso]
    rw [eqToIso_trans]
    exact equality_iso_heq _ _ _ _ _
  have he := pairInto_congr P β
    ((polynomialUnderCoefficient R).app a) ((polynomialUnderCoefficient R).app a)
    (α.app a ≫ (laurentUnderFunctor R).map f)
    ((polynomialUnderFunctor R).map f ≫ α.app b) rfl (α.naturality f).symm
    (CoefficientBassRaw1PolynomialCommonSheet.reference P α f) _ _ hi
  ext z
  have hm := CoefficientBassPolynomialSheetNormalization.map_comp
    (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P
      ((polynomialUnderCoefficient R).app a) ((polynomialUnderFunctor R).map f ≫ α.app b))
    (CoefficientBassRaw1PolynomialPostcomp.reference P ((polynomialUnderCoefficient R).app a)
      ((polynomialUnderFunctor R).map f) (α.app b))
    (CoefficientBassRaw1PolynomialCommonSheet.reference P α f)
    (CoefficientBassRaw1PolynomialCommonSheet.chart P β (b := b))
    (CoefficientBassRaw1PolynomialPausedChart.sheetReference P β
      ((polynomialUnderCoefficient R).app a) ((polynomialUnderFunctor R).map f ≫ α.app b))
    (Iso.refl _)
    (CoefficientBassRaw1PolynomialRadialCaps.rightPolynomialIso P
      ((polynomialUnderCoefficient R).app a) ((polynomialUnderFunctor R).map f) (α.app b))
    (CoefficientBassRaw1PolynomialRectangle.middleAnchor P α f)
    (CoefficientBassRaw1PolynomialPairCone.corrected P β
      ((polynomialUnderCoefficient R).app a) ((polynomialUnderFunctor R).map f ≫ α.app b) z)
  exact (ContinuousMap.congr_fun he z).trans hm.symm

/-- The middle and last left caps are the same entire original corrected radial face. -/
theorem middle_left_eq_last_left {R : CommRingCat.{u}} (P : Over (Spec R))
    (α β : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    {a b : Under R} (f : a ⟶ b) :
    middleLeft P α β f = lastLeft P α β f := by
  obtain ⟨hM, ehM⟩ := middle_anchor_equality P α f
  obtain ⟨hL, ehL⟩ := last_anchor_equality P α f
  have hi : HEq
      (CoefficientBassRaw1PolynomialRectangle.middleAnchor P α f ≪≫
        CoefficientBassRaw1PolynomialRadialCaps.leftPolynomialIso P
          ((polynomialUnderCoefficient R).app a) ((polynomialUnderFunctor R).map f) (α.app b))
      (CoefficientBassRaw1PolynomialRectangle.lastAnchor P α f ≪≫
        CoefficientBassRaw1PolynomialRadialCaps.leftPolynomialIso P f
          ((polynomialUnderCoefficient R).app b) (α.app b)) := by
    rw [ehM, ehL]
    dsimp only [CoefficientBassRaw1PolynomialRadialCaps.leftPolynomialIso]
    rw [eqToIso_trans, eqToIso_trans]
    exact equality_iso_heq _ _ _ _ _
  have he := pairInto_congr P β
    ((polynomialUnderCoefficient R).app a ≫ (polynomialUnderFunctor R).map f)
    (f ≫ (polynomialUnderCoefficient R).app b) (α.app b) (α.app b)
    ((polynomialUnderCoefficient R).naturality f).symm rfl
    (CoefficientBassRaw1PolynomialCommonSheet.reference P α f) _ _ hi
  ext z
  have hm := CoefficientBassPolynomialSheetNormalization.map_comp
    (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P
      ((polynomialUnderCoefficient R).app a ≫ (polynomialUnderFunctor R).map f) (α.app b))
    (CoefficientBassRaw1PolynomialPostcomp.reference P ((polynomialUnderCoefficient R).app a)
      ((polynomialUnderFunctor R).map f) (α.app b))
    (CoefficientBassRaw1PolynomialCommonSheet.reference P α f)
    (CoefficientBassRaw1PolynomialCommonSheet.chart P β (b := b))
    (CoefficientBassRaw1PolynomialPausedChart.sheetReference P β
      ((polynomialUnderCoefficient R).app a ≫ (polynomialUnderFunctor R).map f) (α.app b))
    (Iso.refl _)
    (CoefficientBassRaw1PolynomialRadialCaps.leftPolynomialIso P
      ((polynomialUnderCoefficient R).app a) ((polynomialUnderFunctor R).map f) (α.app b))
    (CoefficientBassRaw1PolynomialRectangle.middleAnchor P α f)
    (CoefficientBassRaw1PolynomialPairCone.corrected P β
      ((polynomialUnderCoefficient R).app a ≫ (polynomialUnderFunctor R).map f) (α.app b) z)
  have hl := CoefficientBassPolynomialSheetNormalization.map_comp
    (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P
      (f ≫ (polynomialUnderCoefficient R).app b) (α.app b))
    (CoefficientBassRaw1PolynomialPostcomp.reference P f
      ((polynomialUnderCoefficient R).app b) (α.app b))
    (CoefficientBassRaw1PolynomialCommonSheet.reference P α f)
    (CoefficientBassRaw1PolynomialCommonSheet.chart P β (b := b))
    (CoefficientBassRaw1PolynomialPausedChart.sheetReference P β
      (f ≫ (polynomialUnderCoefficient R).app b) (α.app b))
    (Iso.refl _)
    (CoefficientBassRaw1PolynomialRadialCaps.leftPolynomialIso P f
      ((polynomialUnderCoefficient R).app b) (α.app b))
    (CoefficientBassRaw1PolynomialRectangle.lastAnchor P α f)
    (CoefficientBassRaw1PolynomialPairCone.corrected P β
      (f ≫ (polynomialUnderCoefficient R).app b) (α.app b) z)
  exact hm.trans ((ContinuousMap.congr_fun he z).trans hl.symm)

end Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialCommonRadialSeams
