/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterAuxiliaryNegativeBoundarySign

/-! A separate-package original auxiliary negative-class cancellation consumer. -/
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.PerfectComplexes
open GlobalSectionChangeIndex ParameterAuxiliarySupport GlobalAuxiliaryParameterCoefficient
universe u
namespace Consumer

attribute [local instance] fiberNegativeFineClass_isIso

/-- Passing to the actual fine fiber comparison cannot identify distinct original negative maps. -/
theorem auxiliaryFineNegativeClass_cancel
    {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q)
    [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]
    [QuasiSeparatedSpace Q.left] (T : Q.left.Opens) [CompactSpace T]
    (i : ℕ) (a : Under (CommRingCat.of (ULift.{u} ℤ))) (A : AddCommGrpCat.{u + 1})
    (x y : A ⟶ (Quillen.PerfectComplexes.Bass.supportedNegativeKFunctor i).obj
      ((boundedFlatCoefficientQuasiCompactOpenPairRow
        (supportArrow Q (unionOpen f.left T))).obj a))
    (h : x ≫ fiberNegativeFineClass f T i a = y ≫ fiberNegativeFineClass f T i a) :
    x = y := (cancel_mono (fiberNegativeFineClass f T i a)).1 h

end Consumer
