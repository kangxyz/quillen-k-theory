/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.RingTheory.RegularLocalRing.Defs

/-! # Dimension-zero regular local rings

The actual regularity definition identifies the maximal-ideal generator count
with Krull dimension. In dimension zero the maximal ideal vanishes, so the ring
is a field, with no domain or resolution hypothesis.
-/
@[expose] public section

noncomputable section
universe u
open IsLocalRing

namespace Quillen.RegularLocal

/-- The dimension-zero case of regular local algebra: the maximal ideal has
no generators, so it is zero and the ring is a field. -/
theorem isField_of_regularLocal_dimension_zero (R : Type u) [CommRing R]
    [IsRegularLocalRing R] (h : ringKrullDim R = 0) : IsField R := by
  apply isField_iff_maximalIdeal_eq.mpr
  apply (Submodule.spanFinrank_eq_zero_iff_eq_bot (maximalIdeal R).fg_of_isNoetherianRing).mp
  have h' := IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)
  rw [h] at h'
  exact_mod_cast h'

end Quillen.RegularLocal
