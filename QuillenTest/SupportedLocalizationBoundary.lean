/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import Quillen.AlgebraicGeometry.PerfectComplexes.Bass.SupportedLocalizationBoundary

/-! Original negative boundary composites and the exact splice at supported K₀. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.hashCommand false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
universe u
namespace Quillen.PerfectComplexes.Bass
variable (A : QuasiCompactOpenPairs.{u}) [CompactSpace A.obj.obj.left]
  [QuasiSeparatedSpace A.obj.obj.right]

example (i : ℕ) :
    (supportedNegativeKForget A (i + 1) : _ → _).comp
      (supportedNegativeLocalizationConnecting A i) = 0 :=
  (supportedNegativeLocalizationConnecting_exact_supported A i).comp_eq_zero

example :
    (supportedNegativeKForget A 0 : _ → _).comp
      (qcqsPerfectConnectingHom A.obj.obj.hom 0).toAdditive = 0 :=
  (supportedLocalization_zeroTail A).1.comp_eq_zero

example (x : supportedNegativeK A 1) :
    supportedNegativeKForget A 1 x = 0 ↔
      ∃ y : Additive (PerfectK A.obj.obj.left 0),
        supportedNegativeLocalizationConnecting A 0 y = x :=
  (supportedLocalization_zeroTail A).2.2.2 x

#print axioms boundedFlatCoefficientFineLocalizationConnecting_exact_open
#print axioms boundedFlatCoefficientNegativeLocalizationConnecting_comparison
#print axioms boundedFlatCoefficientNegativeLocalizationConnecting_exact_supported
#print axioms supportedNegativeLocalizationLongExactSequence
#print axioms supportedLocalization_zeroTail
end Quillen.PerfectComplexes.Bass
