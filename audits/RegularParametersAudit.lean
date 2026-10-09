import Quillen.Algebra.RegularLocal.Parameters

/-! Contract and axiom audit of the actual regular-local first-parameter theorem. -/

open IsLocalRing Quillen.RegularLocal
universe u

example (R : Type u) [CommRing R] [IsRegularLocalRing R] : IsDomain R :=
  isDomain_of_regularLocal R

example (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (d : ℕ) (hd : ringKrullDim R = (d + 1 : ℕ)) :
    ∃ x : R, x ∈ maximalIdeal R ∧ IsSMulRegular R x ∧
      IsRegularLocalRing (R ⧸ Ideal.span {x}) ∧
      ringKrullDim (R ⧸ Ideal.span {x}) = (d : ℕ) :=
  exists_regular_parameter R d hd

#print axioms exists_parameter_avoiding_minimalPrimes
#print axioms isDomain_of_prime_parameter
#print axioms exists_generators_containing_parameter
#print axioms spanFinrank_maximalIdeal_quotient_parameter_le
#print axioms regularLocal_quotient_parameter
#print axioms isField_of_regularLocal_dimension_zero
#print axioms isDomain_of_regularLocal_dimension
#print axioms isDomain_of_regularLocal
#print axioms isSMulRegular_of_regularLocal_ne_zero
#print axioms exists_regular_parameter

#check isDomain_of_regularLocal
#check regularLocal_quotient_parameter
#check exists_regular_parameter
