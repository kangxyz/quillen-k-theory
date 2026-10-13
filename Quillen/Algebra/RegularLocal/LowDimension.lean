/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Algebra.RegularLocal.DimensionZero
public import Quillen.Algebra.RegularLocal.PrincipalDomain

/-! # Regular local rings of dimension at most one

Dimension zero gives a field. In dimension at most one, the actual cotangent
space condition makes the maximal ideal principal. Krull intersection supplies
the domain property in positive dimension, and then every ideal is principal.
No projective-dimension or resolution hypothesis is imposed.
-/
@[expose] public section

noncomputable section
universe u
open IsLocalRing

namespace Quillen.RegularLocal

/-- Low-dimensional local regularity implies the domain property. The
positive-dimensional case is proved using a principal maximal ideal and
Krull intersection, while dimension zero is already a field. -/
theorem isDomain_of_dimension_le_one (R : Type u) [CommRing R]
    [IsRegularLocalRing R] (h : ringKrullDim R ≤ 1) : IsDomain R := by
  by_cases hzero : ringKrullDim R = 0
  · let := (isField_of_regularLocal_dimension_zero R hzero).toField
    infer_instance
  · have he := (IsRegularLocalRing.iff_finrank_cotangentSpace R).mp inferInstance
    have hd : Module.finrank (ResidueField R) (CotangentSpace R) ≤ 1 := by
      exact_mod_cast he.trans_le h
    exact isDomain_of_principal_maximalIdeal R (finrank_cotangentSpace_le_one_iff.mp hd) hzero

/-- A regular local ring of dimension at most one is a PID. Both the domain
property and principal ideal property are derived from regularity. -/
theorem isPrincipalIdealRing_of_dimension_le_one (R : Type u) [CommRing R]
    [IsRegularLocalRing R] (h : ringKrullDim R ≤ 1) :
    IsPrincipalIdealRing R := by
  have := isDomain_of_dimension_le_one R h
  have he := (IsRegularLocalRing.iff_finrank_cotangentSpace R).mp inferInstance
  have hd : Module.finrank (ResidueField R) (CotangentSpace R) ≤ 1 := by
    exact_mod_cast he.trans_le h
  exact ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain R).out 6 1).mp hd

end Quillen.RegularLocal
