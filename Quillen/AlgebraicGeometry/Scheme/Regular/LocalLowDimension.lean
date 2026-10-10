/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.AlgebraicGeometry.Scheme.Regular.SmallComparison
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Quillen.AlgebraicGeometry.Scheme.Regular.LocalPrincipalDomain

/-!
# Canonical K-to-G comparison from low-dimensional local regularity

These results start with mathlib's geometric dimension definition of a
regular local ring. Dimension zero forces the maximal ideal to vanish.
In dimension at most one the cotangent dimension condition forces the maximal
ideal to be principal. Krull intersection supplies the domain property in
positive dimension, and then every ideal is principal.
No projective-dimension or resolution hypothesis is imposed.

The domain property in dimension at most one is proved here, rather than
assumed. The unrestricted higher-dimensional regularity theorem remains
separate.
-/
@[expose] public section

noncomputable section
universe u
open AlgebraicGeometry IsLocalRing

namespace Quillen.RegularLocal

/-- A zero-dimensional regular local ring is a field, directly from the
maximal-ideal generator count in the actual regularity definition. -/
theorem isField_of_dimension_zero (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (h : ringKrullDim R = 0) : IsField R := by
  apply isField_iff_maximalIdeal_eq.mpr
  apply (Submodule.spanFinrank_eq_zero_iff_eq_bot (maximalIdeal R).fg_of_isNoetherianRing).mp
  have h' := IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)
  rw [h] at h'
  exact_mod_cast h'

/-- Low-dimensional local regularity implies the domain property. The
positive-dimensional case is proved using a principal maximal ideal and
Krull intersection, while dimension zero is already a field. -/
theorem isDomain_of_dimension_le_one (R : Type u) [CommRing R]
    [IsRegularLocalRing R] (h : ringKrullDim R ≤ 1) : IsDomain R := by
  by_cases hzero : ringKrullDim R = 0
  · letI := (isField_of_dimension_zero R hzero).toField
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

namespace Quillen.Scheme

/-- The canonical comparison for a zero-dimensional regular local ring.
The required field structure is derived from regularity. -/
theorem KToG_regularLocal_dimension_zero_bijective (R : CommRingCat.{u})
    [IsRegularLocalRing R] (h : ringKrullDim R = 0) (n : ℕ) :
    Function.Bijective (KToG (Spec R) n) := by
  letI := (RegularLocal.isField_of_dimension_zero R h).toField
  exact KToG_field_bijective R n

/-- The canonical comparison for a regular local ring of dimension at
most one. Both its domain property and finite resolutions are derived. -/
theorem KToG_regularLocal_dimension_le_one_bijective (R : CommRingCat.{u})
    [IsRegularLocalRing R] (h : ringKrullDim R ≤ 1) (n : ℕ) :
    Function.Bijective (KToG (Spec R) n) := by
  have := RegularLocal.isDomain_of_dimension_le_one R h
  have := RegularLocal.isPrincipalIdealRing_of_dimension_le_one R h
  exact KToG_pid_bijective R n

/-- The low-dimensional regular-local comparison, with the original
canonical K-to-G homomorphism as its forward map. -/
def KToGRegularLocalDimOneEquiv (R : CommRingCat.{u})
    [IsRegularLocalRing R] (h : ringKrullDim R ≤ 1) (n : ℕ) :
    K (Spec R) n ≃* G (Spec R) n :=
  MulEquiv.ofBijective (KToG (Spec R) n) (KToG_regularLocal_dimension_le_one_bijective R h n)

/-- The monoid-hom coercion is the canonical forward map. -/
@[simp] theorem KToGRegularLocalDimOneEquiv_coe (R : CommRingCat.{u})
    [IsRegularLocalRing R] (h : ringKrullDim R ≤ 1) (n : ℕ) :
    ↑(KToGRegularLocalDimOneEquiv R h n) = KToG (Spec R) n := rfl

end Quillen.Scheme
