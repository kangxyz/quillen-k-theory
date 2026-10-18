/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Quillen.GTheory.Dedekind.Localization

/-! A field has empty height-one support in the original native torsion category. -/

open scoped nonZeroDivisors

namespace QuillenTest.DedekindResidueSupport

/-- The empty height-one spectrum kills the actual torsion-supported K2 of every field. -/
theorem fieldSupportedKTwo (F : Type*) [Field F]
    (a : Quillen.FiniteModuleLocalization.SupportedG (nonZeroDivisors F) 2) : a = 1 := by
  apply Quillen.DedekindPrimary.supportedK_ext F 2
  intro p
  exact (p.ne_bot ((Ideal.eq_bot_or_top p.asIdeal).resolve_right p.isPrime.ne_top)).elim

end QuillenTest.DedekindResidueSupport
