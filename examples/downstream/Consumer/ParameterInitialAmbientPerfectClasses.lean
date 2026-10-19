/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterInitialAmbientPerfectClasses

/-! # The original ambient zero comparison as an actual client arrow -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.PerfectComplexes
universe u
namespace Consumer.ParameterInitialAmbientPerfectClasses

/-- The entire zero comparison hom is the unchanged original negative-recursion arrow. -/
theorem original_zero_arrow {R : CommRingCat.{u}} (P : Over (Spec R)) [CompactSpace P.left]
    (a : Under R) :
    (boundedFlatCoefficientSectionPerfectKStableEquiv (op P, a) 0).toAddCommGrpIso.hom =
      (boundedFlatCoefficientAmbientBassBottomZeroNatIso P).hom.app a := by
  ext x
  exact boundedFlatCoefficientSectionPerfectKStableEquiv_zero P a x.toMul

end Consumer.ParameterInitialAmbientPerfectClasses
