/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterAmbientDoubleSign

/-! The actual ambient correction preserves arbitrary incoming original negative classes. -/
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.PerfectComplexes
universe u

example (P : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
    [CompactSpace P.left] [QuasiSeparatedSpace P.left]
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) {A : AddCommGrpCat.{u + 1}}
    (g : A ⟶ (Quillen.PerfectComplexes.Bass.negativeKFunctor 2).obj
      ((boundedFlatCoefficientQuasiCompactRow P).obj a)) :
    g ≫ (GlobalParameterCoefficient.negativeClassCorrection P 2 a).hom = g := by
  rw [GlobalParameterCoefficient.negativeClassCorrection_two_hom P a, Category.comp_id]
