/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterCurrentNegativeBoundarySign

/-! Regression properties for unchanged negative classes and the intrinsic boundary. -/
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.PerfectComplexes
open Quillen.PerfectComplexes.ParameterFullCurrentNull
universe u
variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]
  [QuasiSeparatedSpace Q.left]

/-- Arbitrary original supported negative-class maps survive the prescribed finite comparison. -/
example (i : ℕ) (a : Under (CommRingCat.of (ULift.{u} ℤ)))
    {A : AddCommGrpCat.{u + 1}}
    (g : A ⟶ (Quillen.PerfectComplexes.Bass.supportedNegativeKFunctor i).obj
      ((boundedFlatCoefficientQuasiCompactOpenPairRow f).obj a)) :
    g ≫ (GlobalSupportedParameterCoefficient.negativeClassCorrection f i a).hom = g := by
  rw [GlobalSupportedParameterCoefficient.negativeClassCorrection_hom, Category.comp_id]

/-- The intrinsic current boundary annihilates the original restriction in every index. -/
example (i : ℕ) (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (boundedFlatCoefficientOriginalNegativeKRestriction f i).app a ≫
      currentNegativeConnecting f i a = 0 := by
  ext x
  exact (currentNegativeConnecting_exact_open f i a).apply_apply_eq_zero x
