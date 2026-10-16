/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveSupportComposition

/-! Exact strict-inclusion image of the paused positive-cone composition, tracing the entire
original moving-null boundary, its null-comparison tail and actual square lift. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.LoopPrespectrum CommRingCat.PolynomialLaurent
open AlgebraicGeometry.Scheme.BaseChange.Coefficients Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.CoefficientBassPositiveCompositionTrack
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- The entire positive moving-null square maps to the fixed original square on its positive
face. All path pasting, boundary collapse, relative null reassociation and square lifting remain. -/
theorem nullSquare_factor (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a)))).space n) :
    (boundedFlatCoefficientBassPositiveConeInclusion P c).map n
      ((nullSquare P u v).level n (r, (s, x))) =
    (boundedFlatCoefficientBassPositiveSupportSquare P u v).level n
      (r, (s, (HomotopyPushout.inl
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))).map n x)) := by
  unfold nullSquare boundedFlatCoefficientBassPositiveSupportSquare
    coneSquareCompositionMovingNullSquare
  apply Homotopy.RelHomotopy.toSquare_mapped_points
  intro r' s'
  apply Homotopy.RelHomotopy.trans_mapped_points
  · intro r'' s''
    apply Homotopy.Square.toBoundary_mapped_points
    intro r''' s'''
    unfold coneSquareNullMovingSquare
    apply Homotopy.Square.pastePaths_mapped_points
    · intro t w
      exact congrArg ((mappingConeInclusion
        (boundedFlatCoefficientBassSquareComparison P c)).map n)
        (comparisonSquare_inl P u v n t w x)
    · intro t w
      change (mappingConeHomotopy (boundedFlatCoefficientBassSquareComparison P c)).level n
          (w, (HomotopyPushout.inl
            (boundedFlatPerfectPrespectrumMap (polynomialProjection P c))
            (boundedFlatPerfectPrespectrumMap (polynomialProjection P c))).map n
              ((polynomialComposition P u v).level n (t, x))) = _
      exact congrArg (fun y ↦
        (mappingConeHomotopy (boundedFlatCoefficientBassSquareComparison P c)).level n (w, y))
        (polynomialComposition_inl P u v n t x)
  · intro r'' s''
    apply Homotopy.RelHomotopy.hcomp_mapped_points
    · intro r''' s'''
      apply Homotopy.RelHomotopy.hcomp_mapped_points
      · intro _ _
        rfl
      · intro t w
        exact coneSquareCompositionNullComparison_mapped_points
          (boundedFlatPerfectPrespectrumMap (laurentPlus P a))
          (boundedFlatPerfectPrespectrumMap (laurentPlus P b))
          (boundedFlatPerfectPrespectrumMap (laurentPlus P c))
          (boundedFlatPerfectPrespectrumMap
            (coefficientMap P ((polynomialUnderFunctor R).map u)))
          (boundedFlatPerfectPrespectrumMap (coefficientMap P ((laurentUnderFunctor R).map u)))
          (boundedFlatPerfectPrespectrumMap
            (coefficientMap P ((polynomialUnderFunctor R).map v)))
          (boundedFlatPerfectPrespectrumMap (coefficientMap P ((laurentUnderFunctor R).map v)))
          (boundedFlatCoefficientPlusSquareHomotopy P u)
          (boundedFlatCoefficientPlusSquareHomotopy P v)
          (boundedFlatCoefficientBassSquareComparison P a)
          (boundedFlatCoefficientBassSquareComparison P b)
          (boundedFlatCoefficientBassSquareComparison P c)
          (boundedFlatCoefficientPolynomialSpanMap P u)
          (boundedFlatPerfectPrespectrumMap (coefficientMap P ((laurentUnderFunctor R).map u)))
          (boundedFlatCoefficientPolynomialSpanMap P v)
          (boundedFlatPerfectPrespectrumMap (coefficientMap P ((laurentUnderFunctor R).map v)))
          (boundedFlatCoefficientBassComparisonHomotopy P u)
          (boundedFlatCoefficientBassComparisonHomotopy P v)
          (boundedFlatCoefficientBassPositiveConeInclusion P c) n x _
          (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) t w
    · intro _ _
      rfl

/-- The strict inclusion image equals the fixed C1 restriction on the entire positive cone,
retaining both the original Laurent face and every original positive cylinder point. -/
theorem coneComposition_factor (n : ℕ) (r : unitInterval)
    (x : (mappingCone (boundedFlatPerfectPrespectrumMap (laurentPlus P a))).space n) :
    (boundedFlatCoefficientBassPositiveConeInclusion P c).map n
      ((coneComposition P u v).level n (r, x)) =
    (BassMWhole.coneComposition P u v).level n
      (r, (boundedFlatCoefficientBassPositiveConeInclusion P a).map n x) := by
  have h : (coneComposition P u v).at r ≫
      boundedFlatCoefficientBassPositiveConeInclusion P c =
    boundedFlatCoefficientBassPositiveConeInclusion P a ≫
      (BassMWhole.coneComposition P u v).at r := by
    apply mappingCone_hom_ext
    · apply Hom.ext
      funext k
      ext y
      rfl
    · intro k s y
      exact nullSquare_factor P u v k r s y
  exact congrArg (fun k ↦ k.map n x) h

/-- The positive composition is looped with the original independent output-loop parameter. -/
def stepComposition :
    Homotopy (parameterLoopingMap (boundedFlatCoefficientBassPositiveConeMap P (u ≫ v)))
      (parameterLoopingMap (boundedFlatCoefficientBassPositiveConeMap P u) ≫
        parameterLoopingMap (boundedFlatCoefficientBassPositiveConeMap P v)) :=
  (coneComposition P u v).parameterLooping.cast rfl (parameterLoopingFunctor.map_comp _ _)

/-- Every parameter-looped composition value retains the fixed whole-cone C1 restriction. -/
theorem stepComposition_factor (n : ℕ) (r s : unitInterval)
    (x : (parameterLooping
      (mappingCone (boundedFlatPerfectPrespectrumMap (laurentPlus P a)))).space n) :
    (boundedFlatCoefficientBassPositiveConeInclusion P c).map n
      (Path.toContinuousMap ((stepComposition P u v).level n (r, x)) s) =
    Path.toContinuousMap ((BassMWhole.stepComposition P u v).level n
      (r, (parameterLoopingMap (boundedFlatCoefficientBassPositiveConeInclusion P a)).map n x)) s :=
  coneComposition_factor P u v n r (Path.toContinuousMap x s)

/-- The unchanged original seed sees exactly the supported fixed composition at all times. -/
theorem stepComposition_seed (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    (boundedFlatCoefficientBassPositiveConeInclusion P c).map n
      (Path.toContinuousMap ((stepComposition P u v).level n
        (r, (boundedFlatCoefficientBassPositiveConeSeed P a).map n x)) s) =
    Path.toContinuousMap ((BassMWhole.stepComposition P u v).level n
      (r, (boundedFlatCoefficientBassTransition P a).map n x)) s := by
  have hf := stepComposition_factor P u v n r s
    ((boundedFlatCoefficientBassPositiveConeSeed P a).map n x)
  have hs := congrArg (fun k ↦ k.map n x) (boundedFlatCoefficientBassPositiveConeSeed_factor P a)
  exact hf.trans (congrArg (fun y ↦
    Path.toContinuousMap ((BassMWhole.stepComposition P u v).level n (r, y)) s) hs)

end Quillen.PerfectComplexes.CoefficientBassPositiveCompositionTrack
