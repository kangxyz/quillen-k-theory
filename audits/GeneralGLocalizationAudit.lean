import Quillen.Scheme.Coherent.GlobalLocalization
open CategoryTheory AlgebraicGeometry Quillen.CoherentScheme

#print axioms coherent_extension
#print axioms coherentRestriction_essSurj
#print axioms quotientCoherentRestriction_isEquivalence
#print axioms coherentSupportQuotientEquivalence
#print axioms coherentRestriction_isLocalization
#print axioms coherentRestriction_isLocalization_kernel
#print axioms coherentGlobalSupportedGEquiv
#print axioms supportedCoherentInclusionExact
#print axioms coherentGlobalSupportComparison_comp_inclusion
#print axioms globalInclusionGMap
#print axioms globalInclusionGMap_eq_smallKMap
#print axioms globalConnectingHom
#print axioms global_localization_longExact
#print axioms global_localization_canonical_longExact
#print axioms global_localization_GZero_tail
#print axioms global_GZero_surjective

#check @global_localization_longExact
#check @global_localization_canonical_longExact
#check @global_localization_GZero_tail

universe u
example {U X : Scheme.{u}} [IsNoetherian X] [IsLocallyNoetherian U]
    (j : U ⟶ X) [IsOpenImmersion j] :
    (coherentRestriction j).IsLocalization (coherentSupportedAway j).isoModSerre :=
  inferInstance

example {U X : Scheme.{u}} [IsNoetherian X] [IsLocallyNoetherian U]
    (j : U ⟶ X) [IsOpenImmersion j] :
    Function.Surjective (restrictionGMap j 0) := global_GZero_surjective j
