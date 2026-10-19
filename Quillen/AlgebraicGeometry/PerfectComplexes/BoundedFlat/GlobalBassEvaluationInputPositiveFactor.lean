/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputPositiveSupport
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputNaturality
public import Quillen.Topology.Prespectrum.HomotopySquareMappedSupport

/-!
# Exact positive support of the fixed whole mixed evaluation homotopy

The selected positive commuting square is literally the positive face of the already fixed
whole mixed square. Every operation in the original moving-null word preserves that support,
including its original cone reassociation, boundary collapse, and square lift. Consequently the
actual positive mixed homotopy maps to the fixed whole homotopy on every positive-cone point,
and parameter looping retains this equality at its independent loop time.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.GlobalBassEvaluation.InputPositive
open GlobalSectionChangeIndex
variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The fixed whole square restricts to the original selected positive commuting square. -/
theorem square_factor (n : ℕ) (r s : unitInterval)
    (x : (GlobalSchemeLaurentTrack.diagram.obj (op (polynomial.obj Y))).space n) :
    (square g).level n (r, (s, x)) =
      (InputCube.square g).level n
        (r, (s, (HomotopyPushout.inl (sectionMap (projection.app Y))
          (sectionMap (projection.app Y))).map n x)) := rfl

/-- The complete positive moving null maps to the fixed whole null surface at every coordinate. -/
theorem nullSquare_factor (n : ℕ) (r s : unitInterval)
    (x : (GlobalSchemeLaurentTrack.diagram.obj (op (polynomial.obj Y))).space n) :
    (GlobalRawBass.InputIdentityPositive.inclusion X).map n
      ((nullSquare g).level n (r, (s, x))) =
      (InputNaturality.originalNullSquare g).level n
        (r, (s, (HomotopyPushout.inl (sectionMap (projection.app Y))
          (sectionMap (projection.app Y))).map n x)) := by
  change (GlobalRawBass.InputIdentityPositive.inclusion X).map n
    ((nullSquare g).level n (r, (s, x))) =
    (coneSquareCompositionMovingNullSquare
      (StrictSquare.comparison (sectionSquare Y))
      (GlobalRawBass.comparison Y) (GlobalRawBass.comparison X)
      (spanEvaluation Y) (GlobalBassEvaluation.evaluation (laurent.obj Y))
      (GlobalRawBass.spanMap g) (boundedFlatPerfectPrespectrumMap (laurent.map g))
      (comparisonHomotopy Y) (GlobalRawBass.inputComparisonHomotopy g)
      (InputComparisonTracks.source g) (inputSpanHomotopy g)
      (evaluationComparison (laurent.map g)) (InputCube.square g)).level n
      (r, (s, (HomotopyPushout.inl (sectionMap (projection.app Y))
        (sectionMap (projection.app Y))).map n x))
  unfold nullSquare coneSquareCompositionMovingNullSquare
  apply Homotopy.RelHomotopy.toSquare_mapped_points
  intro r' s'
  apply Homotopy.RelHomotopy.trans_mapped_points
  · intro r'' s''
    apply Homotopy.Square.toBoundary_mapped_points
    intro r''' s'''
    unfold coneSquareNullMovingSquare
    apply Homotopy.Square.pastePaths_mapped_points
    · intro t w
      rfl
    · intro t w
      rfl
  · intro r'' s''
    apply Homotopy.RelHomotopy.hcomp_mapped_points
    · intro r''' s'''
      apply Homotopy.RelHomotopy.hcomp_mapped_points
      · intro _ _
        rfl
      · intro t w
        apply coneSquareCompositionNullComparison_mapped_points
        · intro _
          rfl
        · intro _
          rfl
        · intro _
          rfl
    · intro _ _
      rfl

/-- The actual positive mixed homotopy equals the fixed whole homotopy on all supported points. -/
theorem coneHomotopy_factor (n : ℕ) (r : unitInterval)
    (x : (mappingCone (strictChart Y)).space n) :
    (GlobalRawBass.InputIdentityPositive.inclusion X).map n
      ((coneHomotopy g).level n (r, x)) =
      (InputNaturality.coneHomotopy g).level n (r, (strictInclusion Y).map n x) := by
  have h : (coneHomotopy g).at r ≫ GlobalRawBass.InputIdentityPositive.inclusion X =
      strictInclusion Y ≫ (InputNaturality.coneHomotopy g).at r := by
    apply mappingCone_hom_ext
    · apply Hom.ext
      funext k
      ext y
      rfl
    · intro k s y
      exact nullSquare_factor g k r s y
  exact congrArg (fun k ↦ k.map n x) h

/-- Parameter-looped positive input naturality keeps its original cone homotopy. -/
def stepHomotopy : Homotopy
    (parameterLoopingMap (strictInput g) ≫ parameterLoopingMap (evaluation X))
    (parameterLoopingMap (evaluation Y) ≫
      parameterLoopingMap (GlobalRawBass.InputIdentityPositive.coneMap g)) :=
  (coneHomotopy g).parameterLooping.cast
    (parameterLoopingFunctor.map_comp (strictInput g) (evaluation X))
    (parameterLoopingFunctor.map_comp (evaluation Y)
      (GlobalRawBass.InputIdentityPositive.coneMap g))

/-- Every positive loop retains the exact fixed whole homotopy at both independent times. -/
theorem stepHomotopy_factor (n : ℕ) (r s : unitInterval)
    (γ : (parameterLooping (mappingCone (strictChart Y))).space n) :
    (GlobalRawBass.InputIdentityPositive.inclusion X).map n
      (Path.toContinuousMap ((stepHomotopy g).level n (r, γ)) s) =
      Path.toContinuousMap ((InputNaturality.stepHomotopy g).level n
        (r, (parameterLoopingMap (strictInclusion Y)).map n γ)) s :=
  coneHomotopy_factor g n r (Path.toContinuousMap γ s)

end Quillen.PerfectComplexes.GlobalBassEvaluation.InputPositive
