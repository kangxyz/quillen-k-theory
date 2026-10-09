import Quillen.Scheme.Coherent.Localization.ObjectExtension
open CategoryTheory AlgebraicGeometry Quillen.CoherentScheme

#print axioms isIso_restrict_map_of_le
#print axioms isIso_restrict_map_of_opensRange
#print axioms coherent_of_restrict_top
#print axioms coherent_subobject_on_compact_open_of_enlargement
#print axioms coherent_subobject_extension_of_affine_enlargement
#print axioms exists_coherent_subsheaf_restrict_isIso_noetherian
#print axioms coherent_subobject_extension_noetherian
#print axioms coherent_extension
#print axioms coherentRestriction_essSurj

universe u
example {U X : Scheme.{u}} [IsNoetherian X] [IsLocallyNoetherian U]
    (j : U ⟶ X) [IsOpenImmersion j] :
    (coherentRestriction j).EssSurj := inferInstance
