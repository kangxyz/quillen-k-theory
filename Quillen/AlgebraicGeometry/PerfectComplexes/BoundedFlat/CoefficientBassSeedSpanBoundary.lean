/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassCompositeActualMixedFiller
public import Quillen.Topology.Prespectrum.RelativeHomotopySquarePasting
public import Quillen.Topology.Prespectrum.RelativeHomotopyLevels

/-! Cancel the shared original seed comparison for two equal coefficient composites. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open Quillen.LoopPrespectrum CommRingCat.PolynomialLaurent
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace Quillen.PerfectComplexes.CoefficientBassSeedSpanBoundary
private theorem symm_cast_apply {E F : LoopPrespectrum.{u}}
    {f g f' g' : E ⟶ F} (H : Homotopy f g) (hf : f = f') (hg : g = g')
    (n : ℕ) (r : unitInterval) (x : E.space n) :
    H.symm.level n (r, x) = (H.cast hf hg).symm.level n (r, x) := rfl

variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b b' c : Under R} (p : a ⟶ b) (q : b ⟶ c)
  (p' : a ⟶ b') (q' : b' ⟶ c) (h : p ≫ q = p' ≫ q')

/-- First original coefficient composition followed by the target seed. -/
abbrev Dp := (boundedFlatCoefficientCompositionHomotopy P p q).postcomp
  (boundedFlatCoefficientBassTransition P c)
/-- Second composition with only its equal-composite source endpoint transported. -/
def Dm := ((boundedFlatCoefficientCompositionHomotopy P p' q').postcomp
  (boundedFlatCoefficientBassTransition P c)).cast
    (congrArg (fun k ↦ boundedFlatPerfectPrespectrumMap (coefficientMap P k) ≫
      boundedFlatCoefficientBassTransition P c) h.symm) rfl
/-- Both routes retain this single chosen whole seed comparison. -/
abbrev T := (boundedFlatCoefficientBassTransitionCoefficientHomotopy P (p ≫ q)).symm
/-- The first precomposed seed track. -/
def Lp := (Homotopy.precomp (boundedFlatPerfectPrespectrumMap (coefficientMap P p))
  (boundedFlatCoefficientBassTransitionCoefficientHomotopy P q).symm).cast
    (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm
/-- The first postcomposed seed track. -/
abbrev Pp := (boundedFlatCoefficientBassTransitionCoefficientHomotopy P p).symm.postcomp
  (boundedFlatCoefficientBassStepMap P q)
/-- The first selected whole Bass composition track after the source seed. -/
def Kp := (Homotopy.precomp (boundedFlatCoefficientBassTransition P a)
  (BassMWhole.stepComposition P p q)).cast rfl (Category.assoc _ _ _).symm
/-- The second precomposed seed track. -/
def Lm := (Homotopy.precomp (boundedFlatPerfectPrespectrumMap (coefficientMap P p'))
  (boundedFlatCoefficientBassTransitionCoefficientHomotopy P q').symm).cast
    (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm
/-- The second postcomposed seed track. -/
abbrev Pm := (boundedFlatCoefficientBassTransitionCoefficientHomotopy P p').symm.postcomp
  (boundedFlatCoefficientBassStepMap P q')
/-- The second selected composition, retaining the explicit equal-composite source cast. -/
def Km := (Homotopy.precomp (boundedFlatCoefficientBassTransition P a)
  (BassMWhole.stepComposition P p' q')).cast
    (congrArg (fun k ↦ boundedFlatCoefficientBassTransition P a ≫
      boundedFlatCoefficientBassStepMap P k) h.symm) (Category.assoc _ _ _).symm

/-- Equality of the coefficient composite changes no value of the original second filler. -/
def secondComparison : ((Lm P p' q').trans (Pm P p' q')).RelHomotopy
    ((Dm P p q p' q' h).symm.trans ((T P p q).trans (Km P p q p' q' h))) :=
  Homotopy.RelHomotopy.ofLevels
    (CoefficientBassCompositeActualMixedFiller.originalComparison P p' q') _ _
    (fun _ ↦ rfl) (by
      intro n
      apply Homotopy.trans_level_congr
      · apply ContinuousMap.ext
        rintro ⟨r, x⟩
        have he := symm_cast_apply
          ((boundedFlatCoefficientCompositionHomotopy P p' q').postcomp
            (boundedFlatCoefficientBassTransition P c))
          (congrArg (fun k ↦ boundedFlatPerfectPrespectrumMap (coefficientMap P k) ≫
            boundedFlatCoefficientBassTransition P c) h.symm) rfl n r x
        exact he.symm
      · apply Homotopy.trans_level_congr
        · exact congrArg (fun k ↦
            (boundedFlatCoefficientBassTransitionCoefficientHomotopy P k).symm.level n) h
        · have he := Homotopy.cast_level
            (Homotopy.precomp (boundedFlatCoefficientBassTransition P a)
              (BassMWhole.stepComposition P p' q'))
            (congrArg (fun k ↦ boundedFlatCoefficientBassTransition P a ≫
              boundedFlatCoefficientBassStepMap P k) h.symm)
            (Category.assoc _ _ _).symm n
          have he' := Homotopy.cast_level
            (Homotopy.precomp (boundedFlatCoefficientBassTransition P a)
              (BassMWhole.stepComposition P p' q'))
            rfl (Category.assoc _ _ _).symm n
          exact he.trans he'.symm)

/-- The actual two proved fillers cancel their common seed track, with all clocks retained. -/
def boundary := Homotopy.RelHomotopy.pasteTwoSquares
  (Dp := Dp P p q) (Dm := Dm P p q p' q' h) (T := T P p q)
  (Lp := Lp P p q) (Pp := Pp P p q) (Kp := Kp P p q)
  (Lm := Lm P p' q') (Pm := Pm P p' q') (Km := Km P p q p' q' h)
  (CoefficientBassCompositeActualMixedFiller.originalComparison P p q)
  (secondComparison P p q p' q' h)

end Quillen.PerfectComplexes.CoefficientBassSeedSpanBoundary
