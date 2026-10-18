/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Quillen.GTheory.DVR.SplitResidue
import Mathlib.RingTheory.PowerSeries.Inverse

/-! A characteristic-zero DVR application with its literal coefficient and residue maps. -/

open scoped nonZeroDivisors

namespace QuillenTest.SplitResidueDvr

/-- Constant inclusion and constant coefficient give actual generic G2 injectivity over Q. -/
theorem rationalPowerSeriesGenericGTwoInjective : Function.Injective
    (Quillen.FiniteModuleLocalization.localizationKMap
      (nonZeroDivisors (PowerSeries ℚ)) 2) :=
  Quillen.SplitResidueDvr.localizationKMap_two_injective
    (PowerSeries.C : ℚ →+* PowerSeries ℚ)
    PowerSeries.constantCoeff PowerSeries.constantCoeff_comp_C
    PowerSeries.ker_coeff_eq_max_ideal

end QuillenTest.SplitResidueDvr
