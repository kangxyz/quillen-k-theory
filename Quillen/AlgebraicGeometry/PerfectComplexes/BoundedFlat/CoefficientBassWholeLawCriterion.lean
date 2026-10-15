/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Quillen.Topology.Prespectrum.ConeMovingSquareLaws
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassConeFaces

/-!
# Coefficient Bass Whole Law Criterion

Exact whole-law obligations for the ORIGINAL coefficient Bass maps.
The definitions below are conditional on the displayed full null squares. Neither the original
Laurent inclusion laws nor the polynomial span law supplies those squares.

The null-square criterion concerns fixed cone maps with the displayed inclusion track.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Quillen.LoopPrespectrum
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} (P : Over (Spec R))

/-- The actual identity inclusion track, with only its endpoint association transported. -/
def boundedFlatCoefficientBassIdentityInclusionTrack (a : Under R) :=
  (boundedFlatCoefficientBassConeIdentityInclusionHomotopy P a).cast rfl
    (Category.comp_id _).symm

/-- Missing data for a whole identity law retaining the original Laurent identity track. -/
abbrev BoundedFlatCoefficientBassIdentityNullSquare (a : Under R) :=
  MappingConeMapNullSquare (boundedFlatCoefficientBassSquareComparison P a)
    (boundedFlatCoefficientBassIdentityInclusionTrack P a)

/-- Conditional descent of the complete identity square, preserving the original raw cone map. -/
def boundedFlatCoefficientBassConeIdentityOfNullSquare (a : Under R)
    (S : BoundedFlatCoefficientBassIdentityNullSquare P a) :
    Homotopy (boundedFlatCoefficientBassConeMap P (𝟙 a))
      (𝟙 (mappingCone (boundedFlatCoefficientBassSquareComparison P a))) :=
  mappingConeHomotopyOfNullSquare (boundedFlatCoefficientBassSquareComparison P a)
    (boundedFlatCoefficientBassIdentityInclusionTrack P a) S

/-- A whole cone identity with the prescribed original inclusion exists exactly when its full
null square does; this is a criterion, not a producer of the missing square. -/
theorem boundedFlatCoefficientBassConeIdentity_iff (a : Under R) :
    (∃ H : Homotopy (boundedFlatCoefficientBassConeMap P (𝟙 a))
      (𝟙 (mappingCone (boundedFlatCoefficientBassSquareComparison P a))),
      ∀ n r y, H.level n (r,
        (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a)).map n y) =
          (boundedFlatCoefficientBassConeIdentityInclusionHomotopy P a).level n (r, y)) ↔
    Nonempty (BoundedFlatCoefficientBassIdentityNullSquare P a) :=
  mappingConeHomotopy_with_inclusion_iff (boundedFlatCoefficientBassSquareComparison P a)
    (boundedFlatCoefficientBassIdentityInclusionTrack P a)

/-- The conditional whole cone identity loops with an independent original path parameter. -/
def boundedFlatCoefficientBassStepIdentityOfNullSquare (a : Under R)
    (S : BoundedFlatCoefficientBassIdentityNullSquare P a) :
    Homotopy (boundedFlatCoefficientBassStepMap P (𝟙 a))
      (𝟙 (parameterLooping (mappingCone (boundedFlatCoefficientBassSquareComparison P a)))) :=
  (boundedFlatCoefficientBassConeIdentityOfNullSquare P a S).parameterLooping.cast rfl
    (parameterLoopingFunctor.map_id _)

variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- Conditional descent of the actual entire composition square, with no replacement cone map. -/
def boundedFlatCoefficientBassConeCompositionOfNullSquare
    (S : BoundedFlatCoefficientBassCompositionNullSquare P u v) :
    Homotopy (boundedFlatCoefficientBassConeMap P (u ≫ v))
      (boundedFlatCoefficientBassConeMap P u ≫ boundedFlatCoefficientBassConeMap P v) :=
  mappingConeHomotopyOfNullSquare (boundedFlatCoefficientBassSquareComparison P a)
    (boundedFlatCoefficientBassConeCompositionInclusionHomotopy P u v) S

/-- The existing face candidate's exact full null-square is necessary and sufficient. -/
theorem boundedFlatCoefficientBassConeComposition_iff :
    (∃ H : Homotopy (boundedFlatCoefficientBassConeMap P (u ≫ v))
      (boundedFlatCoefficientBassConeMap P u ≫ boundedFlatCoefficientBassConeMap P v),
      ∀ n r y, H.level n (r,
        (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a)).map n y) =
          (boundedFlatCoefficientBassConeCompositionInclusionHomotopy P u v).level n (r, y)) ↔
    Nonempty (BoundedFlatCoefficientBassCompositionNullSquare P u v) :=
  mappingConeHomotopy_with_inclusion_iff (boundedFlatCoefficientBassSquareComparison P a)
    (boundedFlatCoefficientBassConeCompositionInclusionHomotopy P u v)

/-- The conditional whole cone composition loops without identifying any homotopy times. -/
def boundedFlatCoefficientBassStepCompositionOfNullSquare
    (S : BoundedFlatCoefficientBassCompositionNullSquare P u v) :
    Homotopy (boundedFlatCoefficientBassStepMap P (u ≫ v))
      (boundedFlatCoefficientBassStepMap P u ≫ boundedFlatCoefficientBassStepMap P v) :=
  (boundedFlatCoefficientBassConeCompositionOfNullSquare P u v S).parameterLooping.cast rfl
    (parameterLoopingFunctor.map_comp _ _)

/-- The original polynomial-cylinder restriction of the required whole null-square has three
independent geometric times before the separate spectrum structure or output-loop coordinate. -/
def boundedFlatCoefficientBassCompositionInterior
    (S : BoundedFlatCoefficientBassCompositionNullSquare P u v) (n : ℕ) :
    C(unitInterval × (unitInterval × (unitInterval ×
      (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n)),
      (mappingCone (boundedFlatCoefficientBassSquareComparison P c)).space n) :=
  ⟨fun z ↦ S.level n (z.1, (z.2.1, HomotopyPushout.cylinder
    (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
    (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)) n z.2.2)), by fun_prop⟩

/-- Restriction at the beginning retains the full direct raw cone cylinder. -/
theorem boundedFlatCoefficientBassCompositionInterior_zero
    (S : BoundedFlatCoefficientBassCompositionNullSquare P u v) (n : ℕ)
    (s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    boundedFlatCoefficientBassCompositionInterior P u v S n (0, (s, (t, x))) =
      (boundedFlatCoefficientBassDirectConeNullTrack P u v).level n
        (s, HomotopyPushout.cylinder
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)) n (t, x)) :=
  S.at_zero n s _

/-- Restriction at the end retains the full composed raw cone cylinder. -/
theorem boundedFlatCoefficientBassCompositionInterior_one
    (S : BoundedFlatCoefficientBassCompositionNullSquare P u v) (n : ℕ)
    (s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    boundedFlatCoefficientBassCompositionInterior P u v S n (1, (s, (t, x))) =
      (boundedFlatCoefficientBassCompositeConeNullTrack P u v).level n
        (s, HomotopyPushout.cylinder
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)) n (t, x)) :=
  S.at_one n s _

end Quillen.PerfectComplexes
