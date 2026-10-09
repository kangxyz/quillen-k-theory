import Quillen.Scheme.Regular.AffineLowDimension

#print axioms Quillen.RegularLocal.exists_mem_pow_not_mem_succ
#print axioms Quillen.RegularLocal.exists_pow_mul_unit
#print axioms Quillen.RegularLocal.dimension_zero_of_nilpotent_generator
#print axioms Quillen.RegularLocal.isDomain_of_principal_maximalIdeal
#print axioms Quillen.RegularLocal.isField_of_dimension_zero
#print axioms Quillen.RegularLocal.isDomain_of_dimension_le_one
#print axioms Quillen.RegularLocal.isPrincipalIdealRing_of_dimension_le_one
#print axioms Quillen.CoherentScheme.hasProjectiveDimensionLE_one_of_regular_dim_le_one
#print axioms Quillen.Scheme.KToG_regular_dimension_le_one_bijective
#print axioms Quillen.Scheme.KToGRegularDimOneEquiv
#print axioms Quillen.Scheme.KToGRegularDimOneEquiv_toMonoidHom

universe u
example (R : CommRingCat.{u}) [IsRegularRing R] (h : ringKrullDim R ≤ 1) (n : ℕ) :
    (Quillen.Scheme.KToGRegularDimOneEquiv R h n).toMonoidHom =
      Quillen.Scheme.KToG (AlgebraicGeometry.Spec R) n := rfl

example : IsRegularRing ℤ := inferInstance
example (n : ℕ) : Function.Bijective (Quillen.Scheme.KToG (AlgebraicGeometry.Spec (.of ℤ)) n) :=
  Quillen.Scheme.KToG_pid_bijective (.of ℤ) n
