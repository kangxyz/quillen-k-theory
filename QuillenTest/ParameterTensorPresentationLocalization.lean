/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterTensorPresentationLocalization
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterTensorPresentationAuxiliary

/-! Original-null and negative-degree regressions for actual tensor ordinary presentations. -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Products
open Quillen.LoopPrespectrum Quillen.KTheory.Bass Quillen.PerfectComplexes
open Quillen.PerfectComplexes.GlobalSectionChangeIndex
universe u
namespace QuillenTest.ParameterTensorPresentationLocalization
open ParameterTensorPresentation ParameterAuxiliarySupport
variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]

/-- Every actual negative stable degree sees the same auxiliary ordinary-presentation lift. -/
theorem original_auxiliary_negative (T : Q.Opens)
    [CompactSpace P] [CompactSpace Q] [QuasiSeparatedSpace Q] [CompactSpace T] (k : ℕ) :
    IsIso ((stableHomotopyFunctor (-(Int.ofNat k + 1))).map
      (auxiliaryLift f T (op integerBase))) :=
  auxiliaryLift_integer_isStableEquivalence f T (-(Int.ofNat k + 1))

/-- The original enlargement remains the actual projection of that same-null fiber lift. -/
theorem original_auxiliary_projection (T : Q.Opens) (X : Scheme.{u}ᵒᵖ) :
    auxiliaryLift f T X ≫ homotopyFiberProjection ((auxiliaryRestriction f T).app X) =
      (auxiliaryEnlargement f T).app X :=
  auxiliaryLift_projection f T X

end QuillenTest.ParameterTensorPresentationLocalization
