/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveActualMixedFiller
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassNegativeMixedRoutes
public import Quillen.Topology.Prespectrum.RelativeHomotopySquarePasting
public import Quillen.Topology.Prespectrum.HomotopySquareOfPasting
public import Quillen.Topology.Prespectrum.PushoutMovingHomotopy
public import Quillen.Topology.Prespectrum.PushoutHomotopySquare

/-! Actual two-chart seed descent. The negative mixed comparison is the sole remaining input. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Quillen.LoopPrespectrum
open Quillen.Waldhausen.IteratedS CommRingCat.PolynomialLaurent
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace Quillen.PerfectComplexes.CoefficientBassSeedPushoutComparison
private theorem symm_cast_apply {E F : LoopPrespectrum.{u}}
    {f g f' g' : E ⟶ F} (H : Homotopy f g) (hf : f = f') (hg : g = g')
    (n : ℕ) (r : unitInterval) (x : E.space n) :
    H.symm.level n (r, x) = (H.cast hf hg).symm.level n (r, x) := rfl

variable {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R)
variable (Jm : (CoefficientBassNegativeMixedRoutes.originalLeft P a).RelHomotopy
  (CoefficientBassNegativeMixedRoutes.originalRight P a))

/-- Cancel the common literal Laurent seed track using the proved positive mixed filler. -/
def boundary := Homotopy.RelHomotopy.pasteTwoSquares
  (Dp := (boundedFlatCoefficientLaurentPlusHomotopy P a).postcomp
    (boundedFlatCoefficientBassTransition P ((laurentUnderFunctor R).obj a)))
  (Dm := (boundedFlatCoefficientLaurentMinusHomotopy P a).postcomp
    (boundedFlatCoefficientBassTransition P ((laurentUnderFunctor R).obj a)))
  (T := (boundedFlatCoefficientBassTransitionCoefficientHomotopy P
    ((laurentUnderCoefficient R).app a)).symm)
  (Lp := (Homotopy.precomp
    (boundedFlatPerfectPrespectrumMap (coefficientMap P ((polynomialUnderCoefficient R).app a)))
    (boundedFlatCoefficientBassTransitionCoefficientHomotopy P
      ((underToLaurent R).app a)).symm).cast
        (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm)
  (Pp := (boundedFlatCoefficientBassTransitionCoefficientHomotopy P
    ((polynomialUnderCoefficient R).app a)).symm.postcomp
      (boundedFlatCoefficientBassStepMap P ((underToLaurent R).app a)))
  (Kp := (Homotopy.precomp (boundedFlatCoefficientBassTransition P a)
    (boundedFlatCoefficientBassSecondPlusHomotopy P a)).cast
      rfl (Category.assoc _ _ _).symm)
  (Lm := (Homotopy.precomp
    (boundedFlatPerfectPrespectrumMap (coefficientMap P ((polynomialUnderCoefficient R).app a)))
    (boundedFlatCoefficientBassTransitionCoefficientHomotopy P
      ((underToLaurentInvert R).app a)).symm).cast
        (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm)
  (Pm := (boundedFlatCoefficientBassTransitionCoefficientHomotopy P
    ((polynomialUnderCoefficient R).app a)).symm.postcomp
      (boundedFlatCoefficientBassStepMap P ((underToLaurentInvert R).app a)))
  (Km := (Homotopy.precomp (boundedFlatCoefficientBassTransition P a)
    (boundedFlatCoefficientBassSecondMinusHomotopy P a)).cast
      rfl (Category.assoc _ _ _).symm)
  (CoefficientBassPositiveActualMixedFiller.originalComparison P a) Jm

/-- The actual target cylinder keeps both original polynomial seed tracks. -/
def targetTrack :=
  (((boundedFlatCoefficientBassTransitionCoefficientHomotopy P ((polynomialUnderCoefficient
    R).app a)).symm).postcomp
    (boundedFlatCoefficientBassStepMap P ((underToLaurent R).app a))).trans
    ((Homotopy.precomp (boundedFlatCoefficientBassTransition P a)
      (boundedFlatCoefficientBassSecondSquareHomotopy P a)).trans
      (((boundedFlatCoefficientBassTransitionCoefficientHomotopy P ((polynomialUnderCoefficient
        R).app a)).symm).symm.postcomp
        (boundedFlatCoefficientBassStepMap P ((underToLaurentInvert R).app a))))

/-- The three-sided boundary has exactly the association required by the moving square. -/
def pastedTrack :=
  ((Homotopy.precomp (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
    ((boundedFlatCoefficientBassTransitionCoefficientHomotopy P ((underToLaurent R).app
      a)).symm)).trans
    (targetTrack P a)).trans
    (Homotopy.precomp (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
      ((boundedFlatCoefficientBassTransitionCoefficientHomotopy P ((underToLaurentInvert R).app
        a)).symm)).symm

/-- The initial boundary is the original Bass track followed by the Laurent seed. -/
theorem source_level (n : ℕ) :
    ((boundedFlatCoefficientBassSquareHomotopy P a).postcomp
      (boundedFlatCoefficientBassTransition P ((laurentUnderFunctor R).obj a))).level n =
      ((boundary P a Jm).at 0).level n := by
  rw [Homotopy.RelHomotopy.at_zero]
  simp only [boundedFlatCoefficientBassSquareHomotopy, Homotopy.postcomp_trans,
    Homotopy.postcomp_symm]

/-- The final boundary is the complete actual target Bass cylinder with the prescribed tracks. -/
theorem target_level (n : ℕ) :
    (pastedTrack P a).level n =
      ((boundary P a Jm).at 1).level n := by
  rw [Homotopy.RelHomotopy.at_one]
  apply Homotopy.trans_level_congr
  · apply Homotopy.trans_level_congr
    · rfl
    · apply Homotopy.trans_level_congr
      · rfl
      · apply Homotopy.trans_level_congr
        · unfold boundedFlatCoefficientBassSecondSquareHomotopy
          rw [Homotopy.precomp_trans, Homotopy.precomp_symm]
          apply Homotopy.trans_level_congr
          · apply ContinuousMap.ext
            rintro ⟨r, x⟩
            have h := symm_cast_apply
              (Homotopy.precomp (boundedFlatCoefficientBassTransition P a)
                (boundedFlatCoefficientBassSecondPlusHomotopy P a))
              rfl (Category.assoc (boundedFlatCoefficientBassTransition P a)
                (boundedFlatCoefficientBassStepMap P ((polynomialUnderCoefficient R).app a))
                (boundedFlatCoefficientBassStepMap P ((underToLaurent R).app a))).symm n r x
            exact h
          · have h := Homotopy.cast_level
              (Homotopy.precomp (boundedFlatCoefficientBassTransition P a)
                (boundedFlatCoefficientBassSecondMinusHomotopy P a))
              rfl (Category.assoc (boundedFlatCoefficientBassTransition P a)
                (boundedFlatCoefficientBassStepMap P ((polynomialUnderCoefficient R).app a))
                (boundedFlatCoefficientBassStepMap P ((underToLaurentInvert R).app a))).symm n
            exact h.symm
        · exact congrArg (fun H ↦ H.level n)
            (Homotopy.postcomp_symm
              ((boundedFlatCoefficientBassTransitionCoefficientHomotopy P
                ((polynomialUnderCoefficient R).app a)).symm)
              (boundedFlatCoefficientBassStepMap P ((underToLaurentInvert R).app a)))
  · rfl

/-- The proved geometric boundary yields the entire relative seed comparison. -/
def pasting :
    ((boundedFlatCoefficientBassSquareHomotopy P a).postcomp
      (boundedFlatCoefficientBassTransition P ((laurentUnderFunctor R).obj a))).RelHomotopy
      (pastedTrack P a) :=
  Homotopy.RelHomotopy.ofLevels (boundary P a Jm) _ _
    (by intro n; simpa only [Homotopy.RelHomotopy.at_zero] using
      source_level P a Jm n)
    (by intro n; simpa only [Homotopy.RelHomotopy.at_one] using
      target_level P a Jm n)

/-- Regroup the original source endpoints for literal pushout descent. -/
def sourceDescTrack :=
  ((boundedFlatCoefficientBassSquareHomotopy P a).postcomp (boundedFlatCoefficientBassTransition
    P ((laurentUnderFunctor R).obj a))).cast
    (Category.assoc _ _ _) (Category.assoc _ _ _)

/-- Regroup the actual target endpoints for the original polynomial span comparison. -/
def targetDescTrack :=
  (targetTrack P a).cast
    (Category.assoc _ _ _) (Category.assoc _ _ _)

/-- The complete pasted boundary on the untransported Laurent seed precompositions. -/
def pastedDescTrack :=
  ((Homotopy.precomp (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
    ((boundedFlatCoefficientBassTransitionCoefficientHomotopy P ((underToLaurent R).app
      a)).symm)).trans
    (targetDescTrack P a)).trans
    (Homotopy.precomp (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
      ((boundedFlatCoefficientBassTransitionCoefficientHomotopy P ((underToLaurentInvert R).app
        a)).symm)).symm

/-- The original geometric seed boundary in the exact moving-descent interface. -/
def descPasting :
    (sourceDescTrack P a).RelHomotopy
      (pastedDescTrack P a) :=
  Homotopy.RelHomotopy.ofLevels (pasting P a Jm) _ _ (fun _ ↦ rfl)
    (by
      intro n
      apply Homotopy.trans_level_congr
      · apply Homotopy.trans_level_congr <;> rfl
      · rfl)


/-- Apply the original seed to the two polynomial vertices and retain its actual leg tracks. -/
def spanMap := HomotopyPushout.mapOfHomotopies
  (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
  (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
  (boundedFlatCoefficientBassStepMap P ((polynomialUnderCoefficient R).app a))
  (boundedFlatCoefficientBassStepMap P ((polynomialUnderCoefficient R).app a))
  (boundedFlatCoefficientBassTransition P a)
  (boundedFlatCoefficientBassTransition P ((polynomialUnderFunctor R).obj a))
  (boundedFlatCoefficientBassTransition P ((polynomialUnderFunctor R).obj a))
  (boundedFlatCoefficientBassTransitionCoefficientHomotopy P
    ((polynomialUnderCoefficient R).app a)).symm
  (boundedFlatCoefficientBassTransitionCoefficientHomotopy P
    ((polynomialUnderCoefficient R).app a)).symm

/-- The source descent is exactly the original raw comparison followed by the Laurent seed. -/
theorem sourceDesc_eq :
    HomotopyPushout.desc
      (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
      (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
      (boundedFlatPerfectPrespectrumMap (laurentPlus P a) ≫
        boundedFlatCoefficientBassTransition P ((laurentUnderFunctor R).obj a))
      (boundedFlatPerfectPrespectrumMap (laurentMinus P a) ≫
        boundedFlatCoefficientBassTransition P ((laurentUnderFunctor R).obj a))
      (sourceDescTrack P a) =
    boundedFlatCoefficientBassSquareComparison P a ≫
      boundedFlatCoefficientBassTransition P ((laurentUnderFunctor R).obj a) := by
  apply HomotopyPushout.hom_ext
  · rfl
  · rfl
  · intro n s x
    rfl

/-- The target descent is exactly the seed span map followed by the original second comparison. -/
theorem targetDesc_eq :
    HomotopyPushout.desc
      (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
      (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
      (boundedFlatCoefficientBassTransition P ((polynomialUnderFunctor R).obj a) ≫
        boundedFlatCoefficientBassStepMap P ((underToLaurent R).app a))
      (boundedFlatCoefficientBassTransition P ((polynomialUnderFunctor R).obj a) ≫
        boundedFlatCoefficientBassStepMap P ((underToLaurentInvert R).app a))
      (targetDescTrack P a) =
    spanMap P a ≫ boundedFlatCoefficientBassSecondSquareComparison P a := by
  apply HomotopyPushout.hom_ext
  · rfl
  · rfl
  · intro n s x
    have h : (targetDescTrack P a).level n =
        ((HomotopyPushout.mapSquareHomotopy
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
          (boundedFlatCoefficientBassStepMap P ((polynomialUnderCoefficient R).app a))
          (boundedFlatCoefficientBassStepMap P ((polynomialUnderCoefficient R).app a))
          (boundedFlatCoefficientBassTransition P a)
          (boundedFlatCoefficientBassTransition P ((polynomialUnderFunctor R).obj a))
          (boundedFlatCoefficientBassTransition P ((polynomialUnderFunctor R).obj a))
          (boundedFlatCoefficientBassTransitionCoefficientHomotopy P
            ((polynomialUnderCoefficient R).app a)).symm
          (boundedFlatCoefficientBassTransitionCoefficientHomotopy P
            ((polynomialUnderCoefficient R).app a)).symm).postcomp
              (boundedFlatCoefficientBassSecondSquareComparison P a)).level n := by
      simp only [targetDescTrack, Homotopy.cast_level, targetTrack,
        HomotopyPushout.mapSquareHomotopy, Homotopy.postcomp_trans]
      apply Homotopy.trans_level_congr
      · rfl
      · apply Homotopy.trans_level_congr <;> rfl
    exact DFunLike.congr_fun h (s, x)

/-- The positive filler and the one negative mixed input descend on the original two charts. -/
def comparison :
    Homotopy (boundedFlatCoefficientBassSquareComparison P a ≫
      boundedFlatCoefficientBassTransition P ((laurentUnderFunctor R).obj a))
      (spanMap P a ≫ boundedFlatCoefficientBassSecondSquareComparison P a) :=
  (HomotopyPushout.descSquareHomotopy
    (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
    (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
    (boundedFlatCoefficientBassTransitionCoefficientHomotopy P
      ((underToLaurent R).app a)).symm
    (boundedFlatCoefficientBassTransitionCoefficientHomotopy P
      ((underToLaurentInvert R).app a)).symm
    (descPasting P a Jm).toSquare).cast (sourceDesc_eq P a) (targetDesc_eq P a)

end Quillen.PerfectComplexes.CoefficientBassSeedPushoutComparison
