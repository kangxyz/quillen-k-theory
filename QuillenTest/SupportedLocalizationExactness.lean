/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import Quillen.AlgebraicGeometry.PerfectComplexes.Bass.SupportedLocalizationExactness

/-! Regression for the original open-pair maps, including the genuine supported K₀ image. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.hashCommand false
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
universe u
namespace Quillen.PerfectComplexes.Bass
variable (A : QuasiCompactOpenPairs.{u}) [CompactSpace A.obj.obj.left]
  [QuasiSeparatedSpace A.obj.obj.right]

example (i : ℕ) :
    (negativeKPullback (ObjectProperty.homMk A.obj.obj.hom :
      (⟨A.obj.obj.left, inferInstance⟩ : QuasiCompactSchemes.{u}) ⟶
        quasiCompactOpenPairsBase.obj A) i : _ → _).comp
          (supportedNegativeKForget A i) = 0 :=
  (supportedNegativeK_localization_exact A i).comp_eq_zero

example (y : perfectKZeroFunctor.obj (op (quasiCompactOpenPairsBase.obj A))) :
    perfectKZeroFunctor.map (ObjectProperty.homMk A.obj.obj.hom :
        (⟨A.obj.obj.left, inferInstance⟩ : QuasiCompactSchemes.{u}) ⟶
          quasiCompactOpenPairsBase.obj A).op y = 0 ↔
      ∃ x, supportedKZeroForget.app (op A) x = y :=
  supportedKZero_localization_exact A y

#print axioms supportedNegativeK_localization_exact
#print axioms supportedKZero_localization_exact
end Quillen.PerfectComplexes.Bass
