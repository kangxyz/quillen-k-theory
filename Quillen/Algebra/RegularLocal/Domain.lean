/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Algebra.RegularLocal.ParameterAvoidance
public import Quillen.Algebra.RegularLocal.ParameterQuotient

/-!
# Regular local rings are domains

The domain theorem is proved by induction on the dimension, using minimal
parameter quotients, prime avoidance, and Nakayama's lemma. No domain,
regular-sequence, or finite-resolution hypothesis is assumed.
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

/-- Every regular local ring of a specified finite dimension is a domain.
The induction uses a minimal generator avoiding all minimal primes. -/
theorem isDomain_of_regularLocal_dimension (d : ℕ) (R : Type u) [CommRing R]
    [IsRegularLocalRing R] (hd : ringKrullDim R = (d : ℕ)) : IsDomain R := by
  induction d generalizing R with
  | zero =>
    have hf := isField_of_regularLocal_dimension_zero R (by simpa using hd)
    let := hf.toField
    infer_instance
  | succ d ih =>
    have hne : ringKrullDim R ≠ 0 := by rw [hd]; norm_cast
    obtain ⟨x, hx, hx2, havoid⟩ := exists_parameter_avoiding_minimalPrimes R hne
    obtain ⟨hq, hdim⟩ := regularLocal_quotient_parameter R d hd x hx hx2
    have := hq
    have hdomain := ih (R ⧸ Ideal.span {x}) hdim
    exact isDomain_of_prime_parameter R x hx havoid
      ((Ideal.Quotient.isDomain_iff_prime _).mp hdomain)

/-- A regular local ring is a domain. Its dimension is automatically the
finite natural number of minimal generators of its maximal ideal. -/
theorem isDomain_of_regularLocal (R : Type u) [CommRing R]
    [IsRegularLocalRing R] : IsDomain R :=
  isDomain_of_regularLocal_dimension (maximalIdeal R).spanFinrank R
    IsRegularLocalRing.spanFinrank_maximalIdeal.symm

end Quillen.RegularLocal
