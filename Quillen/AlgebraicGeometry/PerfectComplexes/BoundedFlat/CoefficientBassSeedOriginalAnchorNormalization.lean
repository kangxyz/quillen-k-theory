/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MChartSideRows
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.LaurentUnitReferenceCore
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.NativeReferenceWordCoherence

/-! Normalize the original chart-side anchor without changing its geometric reference. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.CoefficientBassSeedOriginalAnchorNormalization
open BassReferenceMerge BassH0Merge
local notation "N" => boundedFlatNormalizedPullback
local notation "C" => boundedFlatNormalizedPullbackCompIso

private theorem raw_anchor {X Y Z T : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) (w : X ⟶ T)
    (hl : w = (f ≫ g) ≫ h) (hr : w = f ≫ g ≫ h) :
    (eqToIso (congrArg N hl) ≪≫ C (f ≫ g) h) ≪≫ isoWhiskerLeft (N h) (C f g) =
      (eqToIso (congrArg N hr) ≪≫ C f (g ≫ h)) ≪≫
        isoWhiskerRight (C g h) (N f) := by
  have hs := anchored_factorizations_strict f g h (f ≫ g) (g ≫ h) w rfl rfl hl hr
  simpa only [eqToIso_refl, Iso.refl_trans, Iso.trans_assoc] using hs

private theorem small_anchor {X Y Z T : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) (w : X ⟶ T)
    (hl : w = (f ≫ g) ≫ h) (hr : w = f ≫ g ≫ h) :
    smallIso (eqToIso (congrArg N hl) ≪≫ C (f ≫ g) h) ≪≫
        smallIso (isoWhiskerLeft (N h) (C f g)) =
      smallIso (eqToIso (congrArg N hr) ≪≫ C f (g ≫ h)) ≪≫
        smallIso (isoWhiskerRight (C g h) (N f)) :=
  (smallIso_trans _ _).symm.trans
    ((congrArg smallIso (raw_anchor f g h w hl hr)).trans (smallIso_trans _ _))

variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b c : Under R}
  (p : a ⟶ b) (q : b ⟶ c)
  (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  (hc : coefficientMap P (α.app c) ≫ polynomialProjection P c = laurentProjection P c)
local notation "j" => coefficientMap P (α.app c)
local notation "g" => coefficientMap P (CategoryTheory.Functor.map (polynomialUnderFunctor R) q) ≫
  coefficientMap P (CategoryTheory.Functor.map (polynomialUnderFunctor R) p)
local notation "h" => polynomialProjection P a
local notation "w" => laurentProjection P c ≫ coefficientMap P q ≫ coefficientMap P p

include hc

/-- The original geometric total, associated for its normalized polynomial source. -/
theorem chart_total_right : w = j ≫ g ≫ h :=
  (BassOverlap.chart_total P p q α hc).symm.trans (Category.assoc j g h)

/-- The canonical reference to the normalized polynomial composite, with its original transport. -/
def normalizedAnchor : (BassOverlap.commonReference P p q).functor ≅
    (normalizedMap (g ≫ h) ≫ normalizedMap j).functor :=
  smallIso (eqToIso (congrArg N (chart_total_right P p q α hc)) ≪≫ C j (g ≫ h))

/-- The full old chart anchor retains its normalized reference and polynomial normalization. -/
theorem old_side_normalized :
    BassMOuterJoin.oldSideIso P p q α hc =
      normalizedAnchor P p q α hc ≪≫
        isoWhiskerRight (BinaryNormalizationSimplex.total g h) (normalizedMap j).functor := by
  change smallIso (eqToIso (congrArg N (BassOverlap.chart_total P p q α hc).symm) ≪≫
      C (j ≫ g) h) ≪≫
      isoWhiskerLeft (normalizedMap h).functor (smallIso (C j g)) =
    smallIso (eqToIso (congrArg N (chart_total_right P p q α hc)) ≪≫ C j (g ≫ h)) ≪≫
      isoWhiskerRight (smallIso (C g h)) (normalizedMap j).functor
  erw [smallIso_precomp, smallIso_postcomp]
  exact small_anchor j g h w (BassOverlap.chart_total P p q α hc).symm
    (chart_total_right P p q α hc)

/-- The original common-unit sheet keeps the same full normalization with its actual shift. -/
theorem old_side_shifted_normalized :
    LaurentUnitReferenceSpecialization.commonUnit P p q ≪≫
        BassMOuterJoin.oldSideIso P p q α hc =
      (LaurentUnitReferenceSpecialization.commonUnit P p q ≪≫
        normalizedAnchor P p q α hc) ≪≫
          isoWhiskerRight (BinaryNormalizationSimplex.total g h) (normalizedMap j).functor := by
  rw [old_side_normalized, Iso.trans_assoc]

end Quillen.PerfectComplexes.CoefficientBassSeedOriginalAnchorNormalization
