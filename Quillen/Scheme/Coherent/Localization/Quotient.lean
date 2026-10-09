import Quillen.Scheme.Coherent.Localization.Denominators

/-!
# The faithful exact functor from the actual coherent support quotient

The constructed Serre quotient has a canonical functor to coherent sheaves
on the open, and its composite with the quotient functor is exactly actual
restriction. Kernel denominators prove faithfulness on all quotient maps,
not only on maps originally defined on the ambient scheme.

Fullness and essential surjectivity require the geometric coherent
extension theorems. They are deliberately not assumed or asserted here.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.CoherentScheme

variable {U X : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian U]
  (j : U ⟶ X) [IsOpenImmersion j]

/-- The actual categorical quotient by coherent sheaves supported off the open. -/
abbrev CoherentSupportQuotient := (coherentSupportedAway j).isoModSerre.Localization

instance coherentSupportQuotient_abelian : Abelian (CoherentSupportQuotient j) :=
  ObjectProperty.SerreClassLocalization.abelian
    (coherentSupportedAway j).isoModSerre.Q (coherentSupportedAway j)

/-- Restriction descends to the actual constructed coherent Serre quotient. -/
def quotientCoherentRestriction : CoherentSupportQuotient j ⥤ Coherent U :=
  Localization.Construction.lift (coherentRestriction j) (coherentRestriction_inverts_support j)

/-- The descended functor factors actual geometric restriction strictly. -/
theorem quotientCoherentRestriction_fac :
    (coherentSupportedAway j).isoModSerre.Q ⋙ quotientCoherentRestriction j =
      coherentRestriction j :=
  Localization.Construction.fac _ _

/-- The associated natural isomorphism explicitly identifies the quotient
factorization with actual coherent restriction. -/
def quotientCoherentRestriction_facIso :
    (coherentSupportedAway j).isoModSerre.Q ⋙ quotientCoherentRestriction j ≅
      coherentRestriction j := eqToIso (quotientCoherentRestriction_fac j)

@[simp] theorem quotientCoherentRestriction_map_Q {M N : Coherent X} (f : M ⟶ N) :
    (quotientCoherentRestriction j).map ((coherentSupportedAway j).isoModSerre.Q.map f) =
      (coherentRestriction j).map f := by
  simpa only [Functor.comp_map, eqToHom_refl, Category.id_comp, Category.comp_id] using
    Functor.congr_hom (quotientCoherentRestriction_fac j) f

/-- The induced functor is faithful on every quotient morphism, by the
actual coherent kernel denominators and the Serre fraction calculus. -/
instance quotientCoherentRestriction_faithful : (quotientCoherentRestriction j).Faithful := by
  let Q := (coherentSupportedAway j).isoModSerre.Q
  apply Functor.faithful_of_comp_of_hasLeftCalculusOfFractions Q
    (coherentSupportedAway j).isoModSerre (quotientCoherentRestriction j)
  intro M N f g h
  simp only [Q, quotientCoherentRestriction_map_Q] at h
  obtain ⟨M', s, _, hs, hfg⟩ := (coherentRestriction_map_eq_iff_denominator j f g).mp h
  have : IsIso (Q.map s) :=
    Localization.inverts Q (coherentSupportedAway j).isoModSerre s hs
  apply (cancel_epi (Q.map s)).mp
  simpa only [← Q.map_comp] using congrArg Q.map hfg

instance quotientCoherentRestriction_additive : (quotientCoherentRestriction j).Additive := by
  apply (Localization.functor_additive_iff (coherentSupportedAway j).isoModSerre.Q
    (coherentSupportedAway j).isoModSerre _).mpr
  rw [quotientCoherentRestriction_fac]
  infer_instance

instance quotientCoherentRestriction_preservesFiniteLimits :
    PreservesFiniteLimits (quotientCoherentRestriction j) := by
  apply (ObjectProperty.SerreClassLocalization.preservesFiniteLimits_comp_iff
    (coherentSupportedAway j).isoModSerre.Q (coherentSupportedAway j) _).mp
  rw [quotientCoherentRestriction_fac]
  infer_instance

instance quotientCoherentRestriction_preservesFiniteColimits :
    PreservesFiniteColimits (quotientCoherentRestriction j) := by
  apply (ObjectProperty.SerreClassLocalization.preservesFiniteColimits_comp_iff
    (coherentSupportedAway j).isoModSerre.Q (coherentSupportedAway j) _).mp
  rw [quotientCoherentRestriction_fac]
  infer_instance

/-- Exactness of the genuine quotient-induced geometric functor. -/
def quotientCoherentRestrictionExact :
    ExactFunctor (abelianExactStructure (CoherentSupportQuotient j)) (coherentExactStructure U) where
  toFunctor := quotientCoherentRestriction j
  map_conflation _ h := h.map_of_exact _

/-- Two original coherent maps represent the same quotient map precisely
when their actual restrictions agree. -/
theorem coherent_quotient_map_eq_iff {M N : Coherent X} (f g : M ⟶ N) :
    (coherentSupportedAway j).isoModSerre.Q.map f =
      (coherentSupportedAway j).isoModSerre.Q.map g ↔
        (coherentRestriction j).map f = (coherentRestriction j).map g := by
  rw [← quotientCoherentRestriction_map_Q j f, ← quotientCoherentRestriction_map_Q j g]
  exact ⟨congrArg _, fun h => (quotientCoherentRestriction j).map_injective h⟩

/-- A coherent map vanishes on the open exactly when its actual coherent
image is supported in the complement. -/
theorem coherentRestriction_map_eq_zero_iff_image_supported {M N : Coherent X} (f : M ⟶ N) :
    (coherentRestriction j).map f = 0 ↔
      coherentSupportedAway j (Abelian.image f) := by
  rw [← (coherentRestriction j).map_zero M N, ← coherent_quotient_map_eq_iff j f 0]
  rw [Functor.map_zero]
  exact ObjectProperty.SerreClassLocalization.map_eq_zero_iff
    (coherentSupportedAway j).isoModSerre.Q (coherentSupportedAway j) f

/-- The vanishing criterion is the ordinary stalk-support condition on the
image sheaf, rather than an abstract replacement for support. -/
theorem coherentRestriction_map_eq_zero_iff_image_support_subset
    {M N : Coherent X} (f : M ⟶ N) :
    (coherentRestriction j).map f = 0 ↔
      SchemeSheaf.support (Abelian.image f).obj ⊆ (Set.range j)ᶜ := by
  rw [coherentRestriction_map_eq_zero_iff_image_supported,
    coherentSupportedAway_iff_support_subset]

end Quillen.CoherentScheme
