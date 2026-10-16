/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import QuillenTest.TTOriginalMapsIntegration
public import QuillenTest.CoefficientBassSecondStep
public import QuillenTest.CoefficientBassTransitionNaturality
public import QuillenTest.CoefficientBassTransitionStable
public import QuillenTest.CoefficientBassUnitCubeConsumers
public import QuillenTest.CoefficientBassUnitNativeCube
public import QuillenTest.CoefficientBassUnitNativeFaces
public import QuillenTest.CoefficientSupportedBassSeedStable
public import QuillenTest.CommonReferenceNerveParameter
public import QuillenTest.CommonReferenceNerveWhiskering
public import QuillenTest.GenLoopSelfTrackKOne
public import QuillenTest.GodementClosedSectionSpan
public import QuillenTest.MWholeNerveHZero
public import QuillenTest.MWholeNerveSharedStart
public import QuillenTest.MWholeNerveWhiskered
public import QuillenTest.MappingConeShortExact
public import QuillenTest.MappingConeWeakMap
public import QuillenTest.SelfTrackKOperation
public import QuillenTest.SelfTrackKOperationLevelOne
public import QuillenTest.SelfTrackKOperationNaturality
public import QuillenTest.SelfTrackNonnegativeStage
public import QuillenTest.SelfTrackNullEvaluation
public import QuillenTest.SelfTrackPath
public import QuillenTest.SelfTrackStableNaturality
public import QuillenTest.SelfTrackStableNullEvaluation
public import QuillenTest.SelfTrackStableOperation
public import QuillenTest.SelfTrackStableVanishing
public import QuillenTest.SelfTrackSuccessorPositive
public import QuillenTest.StrictLaurentSeedStable
public import QuillenTest.TautologicalCoefficientConeFunctor

/-! # Joint original-map consumers through the stable seed checkpoint -/
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
@[expose] public section
noncomputable section
open CategoryTheory Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
universe u v
namespace QuillenTest.TTStableSeedIntegration
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
variable (W : Quillen.Waldhausen.Structure C) (V : Quillen.Waldhausen.Structure D)
variable {f : originalPrespectrum W ⟶ originalPrespectrum V}

/-- The combined original-map closure retains the exact K-zero representative and inverse. -/
theorem original_kzero_finite_track (H : Homotopy f f) (a : W.K 0) :
    V.smallModelKEquiv 1 (originalKSelfTrackOperation W V H 0 a) =
      (H.homotopyClassOperation 1 0 (W.smallModelKEquiv 0 a))⁻¹ :=
  originalKSelfTrackOperation_levelOne W V H 0 a

end QuillenTest.TTStableSeedIntegration
