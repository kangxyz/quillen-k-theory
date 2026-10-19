/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterCurrentNegativeBoundarySign

/-! Original supported kernel classes come from the intrinsic current boundary. -/
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.PerfectComplexes
open Quillen.PerfectComplexes.ParameterFullCurrentNull
universe u

example {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q)
    [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]
    [QuasiSeparatedSpace Q.left] (i : ℕ) (a : Under (CommRingCat.of (ULift.{u} ℤ)))
    (x : (Quillen.PerfectComplexes.Bass.supportedNegativeKFunctor (i + 1)).obj
      ((boundedFlatCoefficientQuasiCompactOpenPairRow f).obj a))
    (hx : (Quillen.PerfectComplexes.Bass.supportedNegativeKForgetNat (i + 1)).app
      ((boundedFlatCoefficientQuasiCompactOpenPairRow f).obj a) x = 0) :
    ∃ y, currentNegativeConnecting f i a y = x :=
  (currentNegativeConnecting_exact_supported f i a x).mp hx
