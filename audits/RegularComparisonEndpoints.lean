import Quillen.Scheme.Regular.SmallComparison
#print axioms Quillen.Scheme.KToG_field_bijective
#print axioms Quillen.Scheme.KToGFieldEquiv
#print axioms Quillen.CoherentScheme.exists_finiteFree_shortExact
#print axioms Quillen.CoherentScheme.finiteProjectiveResolution_length_le
#print axioms Quillen.CoherentScheme.finiteFreeResolution_length_le_one_of_pid
#print axioms Quillen.CoherentScheme.finiteProjectiveResolutionHypothesis_of_pid
#print axioms Quillen.SchemeSheaf.finiteLocallyFree_tilde_of_finite_projective
#print axioms Quillen.SchemeSheaf.projective_of_finiteLocallyFree_tilde
#print axioms Quillen.SchemeSheaf.finiteLocallyFree_tilde_iff_projective
#print axioms Quillen.SchemeSheaf.coherentResolution_length_le_one_of_pid
#print axioms Quillen.SchemeSheaf.vectorBundleSmallLift_ofEquivalence
#print axioms Quillen.SchemeSheaf.schemeKToG_bijective_of_length_one
#print axioms Quillen.Scheme.KToG_pid_bijective
#print axioms Quillen.Scheme.KToGPIDEquiv
#print axioms Quillen.Scheme.KToGPIDEquiv_toMonoidHom

example (R : CommRingCat) [IsDomain R] [IsPrincipalIdealRing R] (n : ℕ) :
    (Quillen.Scheme.KToGPIDEquiv R n).toMonoidHom =
      Quillen.Scheme.KToG (AlgebraicGeometry.Spec R) n := rfl
