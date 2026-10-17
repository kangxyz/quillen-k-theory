/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPolynomialSheetNormalizationComposition

/-! The common direct endpoint of the two original radial polynomial caps. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.NativePathCells
open scoped Simplicial Topology unitInterval
universe u v
namespace Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialRadialDirectSeam
open CommonReferenceNerve CommonReferenceNerve.CutOpenCarrier
open CoefficientBassRaw1PolynomialSourceCylinder

/-- Equality normalization followed by the literal identity unitor is proof-independent. -/
theorem equality_unitor_heq {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F M N : C ⥤ D) (h : F = M) (k : F = N) :
    HEq (eqToIso h ≪≫ (Functor.leftUnitor M).symm)
      (eqToIso k ≪≫ (Functor.leftUnitor N).symm) := by
  cases h
  cases k
  rfl

/-- Two equality-reference steps retain the same actual identity-source presentation. -/
theorem equality_unitor_two_heq {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F L M K N : C ⥤ D) (h₁ : F = L) (h₂ : L = M) (k₁ : F = K) (k₂ : K = N) :
    HEq (eqToIso h₁ ≪≫ (eqToIso h₂ ≪≫ (Functor.leftUnitor M).symm))
      (eqToIso k₁ ≪≫ (eqToIso k₂ ≪≫ (Functor.leftUnitor N).symm)) := by
  cases h₁
  cases h₂
  cases k₁
  cases k₂
  rfl

variable {R : CommRingCat.{u}} (P : Over (Spec R))

/-- The actual plus direct action in an explicitly fixed polynomial reference. -/
def plusInto {a d : Under R} (f : a ⟶ d) (F : model P a ⟶ model P d)
    (η : F.functor ≅ ((𝟙 (model P a)) ≫ CoefficientBassSeedTargetChartAttachment.M P f).functor) :
    C(carrier P (underToLaurent R) a,
      |firstSimplicial F (CoefficientBassSeedTargetChartAttachment.Jb P (b := d))
        (F ≫ CoefficientBassSeedTargetChartAttachment.Jb P (b := d)) (Iso.refl _)|) :=
  (CoefficientBassPolynomialSheetNormalization.map
    ((𝟙 (model P a)) ≫ CoefficientBassSeedTargetChartAttachment.M P f) F
      (CoefficientBassSeedTargetChartAttachment.Jb P (b := d))
    ((reference P (underToLaurent R) a) ≫ CoefficientBassSeedTargetChartAttachment.L P f)
    (CoefficientBassSeedTargetChartAttachment.targetAnchor P f (𝟙 (model P a))
      (reference P (underToLaurent R) a) (Iso.refl _)) η).comp
    (CoefficientBassPositiveTargetSingleSheet.firstMap P f (𝟙 (model P a))
      (reference P (underToLaurent R) a) (Iso.refl _))

/-- Actual arrow equality transports the whole plus direct map, before evaluation. -/
theorem plusInto_congr {a d : Under R} (f g : a ⟶ d) (h : f = g)
    (F : model P a ⟶ model P d)
    (η : F.functor ≅ ((𝟙 (model P a)) ≫ CoefficientBassSeedTargetChartAttachment.M P f).functor)
    (θ : F.functor ≅ ((𝟙 (model P a)) ≫ CoefficientBassSeedTargetChartAttachment.M P g).functor)
    (hη : HEq η θ) : plusInto P f F η = plusInto P g F θ := by
  subst g
  have hh := eq_of_heq hη
  subst θ
  rfl

/-- The actual minus direct action in an explicitly fixed polynomial reference. -/
def minusInto {a d : Under R} (f : a ⟶ d) (F : model P a ⟶ model P d)
    (η : F.functor ≅ ((𝟙 (model P a)) ≫ CoefficientBassNegativeTargetChartAttachment.M P
      f).functor) :
    C(carrier P (underToLaurentInvert R) a,
      |firstSimplicial F (CoefficientBassNegativeTargetChartAttachment.Jb P (b := d))
        (F ≫ CoefficientBassNegativeTargetChartAttachment.Jb P (b := d)) (Iso.refl _)|) :=
  (CoefficientBassPolynomialSheetNormalization.map
    ((𝟙 (model P a)) ≫ CoefficientBassNegativeTargetChartAttachment.M P f) F
      (CoefficientBassNegativeTargetChartAttachment.Jb P (b := d))
    ((reference P (underToLaurentInvert R) a) ≫ CoefficientBassNegativeTargetChartAttachment.L P f)
    (CoefficientBassNegativeTargetChartAttachment.targetAnchor P f (𝟙 (model P a))
      (reference P (underToLaurentInvert R) a) (Iso.refl _)) η).comp
    (CoefficientBassNegativeTargetSingleSheet.firstMap P f (𝟙 (model P a))
      (reference P (underToLaurentInvert R) a) (Iso.refl _))

/-- Actual arrow equality transports the whole minus direct map, before evaluation. -/
theorem minusInto_congr {a d : Under R} (f g : a ⟶ d) (h : f = g)
    (F : model P a ⟶ model P d)
    (η : F.functor ≅ ((𝟙 (model P a)) ≫ CoefficientBassNegativeTargetChartAttachment.M P f).functor)
    (θ : F.functor ≅ ((𝟙 (model P a)) ≫ CoefficientBassNegativeTargetChartAttachment.M P g).functor)
    (hη : HEq η θ) : minusInto P f F η = minusInto P g F θ := by
  subst g
  have hh := eq_of_heq hη
  subst θ
  rfl


/-- The two actual radial normalizations have the same whole direct polynomial reference. -/
theorem radial_iso_heq {a b c d : Under R} (p : a ⟶ b) (q : b ⟶ c) (w : c ⟶ d) :
    HEq
      (CoefficientBassRaw1PolynomialRadialCaps.leftPolynomialIso P p q w ≪≫
        CoefficientBassRaw1PolynomialPairDirectAction.polynomialIso P (p ≫ q) w)
      (CoefficientBassRaw1PolynomialRadialCaps.rightPolynomialIso P p q w ≪≫
        CoefficientBassRaw1PolynomialPairDirectAction.polynomialIso P p (q ≫ w)) := by
  dsimp only [CoefficientBassRaw1PolynomialRadialCaps.leftPolynomialIso,
    CoefficientBassRaw1PolynomialRadialCaps.rightPolynomialIso,
    CoefficientBassRaw1PolynomialPairDirectAction.polynomialIso,
    CoefficientBassRaw1PolynomialRadialCaps.pairPolynomialIso]
  exact equality_unitor_two_heq _ _ _ _ _
    (congrArg (fun k ↦ (BassH0Merge.normalizedMap k).functor)
      (CoefficientBassRaw1PolynomialRadialCaps.leftPolynomialEq P p q w))
    (CoefficientBassRaw1PolynomialRadialCaps.pairPolynomialEq P (p ≫ q) w)
    (congrArg (fun k ↦ (BassH0Merge.normalizedMap k).functor)
      (CoefficientBassRaw1PolynomialRadialCaps.rightPolynomialEq P p q w))
    (CoefficientBassRaw1PolynomialRadialCaps.pairPolynomialEq P p (q ≫ w))



/-- Both radial plus caps retain the same whole original direct boundary path. -/
theorem plus_radial_zero {a b c d : Under R} (p : a ⟶ b) (q : b ⟶ c) (w : c ⟶ d)
    (s : I) : CoefficientBassRaw1PolynomialRadialCaps.left P (underToLaurent R) p q w (0, s) =
      CoefficientBassRaw1PolynomialRadialCaps.right P (underToLaurent R) p q w (0, s) := by
  let F := CoefficientBassRaw1PolynomialPostcomp.reference P p q w
  let ηL := CoefficientBassRaw1PolynomialRadialCaps.leftPolynomialIso P p q w ≪≫
    CoefficientBassRaw1PolynomialPairDirectAction.polynomialIso P (p ≫ q) w
  let ηR := CoefficientBassRaw1PolynomialRadialCaps.rightPolynomialIso P p q w ≪≫
    CoefficientBassRaw1PolynomialPairDirectAction.polynomialIso P p (q ≫ w)
  have h_left :
      CoefficientBassRaw1PolynomialRadialCaps.left P (underToLaurent R) p q w (0, s) =
        plusInto P ((p ≫ q) ≫ w) F ηL (cylinder P (underToLaurent R) a s) := by
    have hc := congrArg (CoefficientBassRaw1PolynomialRadialCaps.leftMap P (underToLaurent R) p q w)
      (CoefficientBassRaw1PolynomialPairDirectAction.plusPath_corrected_zero P (p ≫ q) w s)
    have hm := CoefficientBassPolynomialSheetNormalization.map_comp
      ((𝟙 (model P a)) ≫ CoefficientBassSeedTargetChartAttachment.M P ((p ≫ q) ≫ w))
      (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P (p ≫ q) w) F
      (CoefficientBassSeedTargetChartAttachment.Jb P (b := d))
      ((reference P (underToLaurent R) a) ≫ CoefficientBassSeedTargetChartAttachment.L P ((p ≫ q)
        ≫ w))
      (CoefficientBassSeedTargetChartAttachment.targetAnchor P ((p ≫ q) ≫ w) (𝟙 (model P a))
        (reference P (underToLaurent R) a) (Iso.refl _))
      (CoefficientBassRaw1PolynomialPairDirectAction.polynomialIso P (p ≫ q) w)
      (CoefficientBassRaw1PolynomialRadialCaps.leftPolynomialIso P p q w)
      (CoefficientBassPositiveTargetSingleSheet.firstMap P ((p ≫ q) ≫ w) (𝟙 (model P a))
        (reference P (underToLaurent R) a) (Iso.refl _) (cylinder P (underToLaurent R) a s))
    exact hc.symm.trans hm
  have h_right :
      CoefficientBassRaw1PolynomialRadialCaps.right P (underToLaurent R) p q w (0, s) =
        plusInto P (p ≫ (q ≫ w)) F ηR (cylinder P (underToLaurent R) a s) := by
    have hc := congrArg (CoefficientBassRaw1PolynomialRadialCaps.rightMap P (underToLaurent R) p
      q w)
      (CoefficientBassRaw1PolynomialPairDirectAction.plusPath_corrected_zero P p (q ≫ w) s)
    have hm := CoefficientBassPolynomialSheetNormalization.map_comp
      ((𝟙 (model P a)) ≫ CoefficientBassSeedTargetChartAttachment.M P (p ≫ (q ≫ w)))
      (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P p (q ≫ w)) F
      (CoefficientBassSeedTargetChartAttachment.Jb P (b := d))
      ((reference P (underToLaurent R) a) ≫ CoefficientBassSeedTargetChartAttachment.L P (p ≫ (q
        ≫ w)))
      (CoefficientBassSeedTargetChartAttachment.targetAnchor P (p ≫ (q ≫ w)) (𝟙 (model P a))
        (reference P (underToLaurent R) a) (Iso.refl _))
      (CoefficientBassRaw1PolynomialPairDirectAction.polynomialIso P p (q ≫ w))
      (CoefficientBassRaw1PolynomialRadialCaps.rightPolynomialIso P p q w)
      (CoefficientBassPositiveTargetSingleSheet.firstMap P (p ≫ (q ≫ w)) (𝟙 (model P a))
        (reference P (underToLaurent R) a) (Iso.refl _) (cylinder P (underToLaurent R) a s))
    exact hc.symm.trans hm
  have he := plusInto_congr P ((p ≫ q) ≫ w) (p ≫ (q ≫ w))
    (Category.assoc p q w) F ηL ηR (radial_iso_heq P p q w)
  exact h_left.trans ((ContinuousMap.congr_fun he (cylinder P (underToLaurent R) a s)).trans
    h_right.symm)

/-- Both radial minus caps retain the same whole original direct boundary path. -/
theorem minus_radial_zero {a b c d : Under R} (p : a ⟶ b) (q : b ⟶ c) (w : c ⟶ d)
    (s : I) : CoefficientBassRaw1PolynomialRadialCaps.left P (underToLaurentInvert R) p q w (0, s) =
      CoefficientBassRaw1PolynomialRadialCaps.right P (underToLaurentInvert R) p q w (0, s) := by
  let F := CoefficientBassRaw1PolynomialPostcomp.reference P p q w
  let ηL := CoefficientBassRaw1PolynomialRadialCaps.leftPolynomialIso P p q w ≪≫
    CoefficientBassRaw1PolynomialPairDirectAction.polynomialIso P (p ≫ q) w
  let ηR := CoefficientBassRaw1PolynomialRadialCaps.rightPolynomialIso P p q w ≪≫
    CoefficientBassRaw1PolynomialPairDirectAction.polynomialIso P p (q ≫ w)
  have h_left :
      CoefficientBassRaw1PolynomialRadialCaps.left P (underToLaurentInvert R) p q w (0, s) =
        minusInto P ((p ≫ q) ≫ w) F ηL (cylinder P (underToLaurentInvert R) a s) := by
    have hc := congrArg (CoefficientBassRaw1PolynomialRadialCaps.leftMap P (underToLaurentInvert
      R) p q w)
      (CoefficientBassRaw1PolynomialPairDirectAction.minusPath_corrected_zero P (p ≫ q) w s)
    have hm := CoefficientBassPolynomialSheetNormalization.map_comp
      ((𝟙 (model P a)) ≫ CoefficientBassNegativeTargetChartAttachment.M P ((p ≫ q) ≫ w))
      (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P (p ≫ q) w) F
      (CoefficientBassNegativeTargetChartAttachment.Jb P (b := d))
      ((reference P (underToLaurentInvert R) a) ≫ CoefficientBassNegativeTargetChartAttachment.L
        P ((p ≫ q) ≫ w))
      (CoefficientBassNegativeTargetChartAttachment.targetAnchor P ((p ≫ q) ≫ w) (𝟙 (model P a))
        (reference P (underToLaurentInvert R) a) (Iso.refl _))
      (CoefficientBassRaw1PolynomialPairDirectAction.polynomialIso P (p ≫ q) w)
      (CoefficientBassRaw1PolynomialRadialCaps.leftPolynomialIso P p q w)
      (CoefficientBassNegativeTargetSingleSheet.firstMap P ((p ≫ q) ≫ w) (𝟙 (model P a))
        (reference P (underToLaurentInvert R) a) (Iso.refl _) (cylinder P (underToLaurentInvert
          R) a s))
    exact hc.symm.trans hm
  have h_right :
      CoefficientBassRaw1PolynomialRadialCaps.right P (underToLaurentInvert R) p q w (0, s) =
        minusInto P (p ≫ (q ≫ w)) F ηR (cylinder P (underToLaurentInvert R) a s) := by
    have hc := congrArg (CoefficientBassRaw1PolynomialRadialCaps.rightMap P (underToLaurentInvert
      R) p q w)
      (CoefficientBassRaw1PolynomialPairDirectAction.minusPath_corrected_zero P p (q ≫ w) s)
    have hm := CoefficientBassPolynomialSheetNormalization.map_comp
      ((𝟙 (model P a)) ≫ CoefficientBassNegativeTargetChartAttachment.M P (p ≫ (q ≫ w)))
      (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P p (q ≫ w)) F
      (CoefficientBassNegativeTargetChartAttachment.Jb P (b := d))
      ((reference P (underToLaurentInvert R) a) ≫ CoefficientBassNegativeTargetChartAttachment.L
        P (p ≫ (q ≫ w)))
      (CoefficientBassNegativeTargetChartAttachment.targetAnchor P (p ≫ (q ≫ w)) (𝟙 (model P a))
        (reference P (underToLaurentInvert R) a) (Iso.refl _))
      (CoefficientBassRaw1PolynomialPairDirectAction.polynomialIso P p (q ≫ w))
      (CoefficientBassRaw1PolynomialRadialCaps.rightPolynomialIso P p q w)
      (CoefficientBassNegativeTargetSingleSheet.firstMap P (p ≫ (q ≫ w)) (𝟙 (model P a))
        (reference P (underToLaurentInvert R) a) (Iso.refl _) (cylinder P (underToLaurentInvert
          R) a s))
    exact hc.symm.trans hm
  have he := minusInto_congr P ((p ≫ q) ≫ w) (p ≫ (q ≫ w))
    (Category.assoc p q w) F ηL ηR (radial_iso_heq P p q w)
  exact h_left.trans ((ContinuousMap.congr_fun he (cylinder P (underToLaurentInvert R) a
    s)).trans h_right.symm)
end Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialRadialDirectSeam
