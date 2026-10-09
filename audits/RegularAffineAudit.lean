import Quillen.Scheme.Regular.Affine

#print axioms Quillen.CoherentScheme.projectiveDimension_ne_top_of_localized
#print axioms Quillen.CoherentScheme.projectiveDimension_ne_top_of_regular
#print axioms Quillen.CoherentScheme.finiteProjectiveResolutionHypothesis_of_regular
#print axioms Quillen.SchemeSheaf.coherentResolutionHypothesis_of_regular
#print axioms Quillen.Scheme.KToG_regular_affine_bijective
#print axioms Quillen.Scheme.KToGRegularAffineEquiv
#print axioms Quillen.Scheme.KToGRegularAffineEquiv_toMonoidHom
#print axioms Quillen.Scheme.KToGRegularAffineEquiv_restrict

universe u
example (R : CommRingCat.{u}) [IsRegularRing R] (n : ℕ) :
    (Quillen.Scheme.KToGRegularAffineEquiv R n).toMonoidHom =
      Quillen.Scheme.KToG (AlgebraicGeometry.Spec R) n := rfl
