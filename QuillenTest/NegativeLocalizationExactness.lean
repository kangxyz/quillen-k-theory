/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientNegativeLocalizationExactness

/-! Original negative localization maps and the degree-zero supported image. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.hashCommand false
open CategoryTheory AlgebraicGeometry
namespace Quillen.PerfectComplexes
universe u
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]
  [QuasiSeparatedSpace Q.left]

example (i : ℕ) (a : Under R) :
    ((boundedFlatCoefficientOriginalNegativeKRestriction f i).app a : _ → _).comp
      ((Bass.supportedNegativeKForgetNat i).app
        ((boundedFlatCoefficientQuasiCompactOpenPairRow f).obj a)) = 0 :=
  (boundedFlatCoefficientSupportedNegativeK_localization_exact f i a).comp_eq_zero

example (a : Under R)
    (y : Bass.perfectKZeroFunctor.obj ((boundedFlatCoefficientQuasiCompactRow Q).obj a)) :
    Bass.perfectKZeroFunctor.map
        ((boundedFlatCoefficientQuasiCompactRowRestriction f).app a) y = 0 ↔
      ∃ x, Bass.supportedKZeroForget.app
        ((boundedFlatCoefficientQuasiCompactOpenPairRow f).obj a) x = y :=
  boundedFlatCoefficientSupportedKZero_localization_exact f a y

#print axioms boundedFlatCoefficientSupportedBassTelescope_fullOpen_exact
#print axioms boundedFlatCoefficientSupportedNegativeK_localization_exact
#print axioms boundedFlatCoefficientSupportedKZero_localization_exact
end Quillen.PerfectComplexes
