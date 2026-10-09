import Quillen.Scheme.Coherent.Affine.Comparison
import Quillen.Scheme.Coherent.Affine.RestrictionExact
import Quillen.Scheme.Coherent.Restriction

/-!
# Principal restriction of the global coherent category

The identity-on-sheaves affine comparison intertwines actual global coherent
restriction and the previously constructed actual affine restriction. Its
proved equivalences transport the Serre-localization universal property.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.CoherentScheme

variable (R : CommRingCat.{u}) [IsNoetherianRing R] (r : R)

/-- The global/affine comparison square for actual principal-open restriction.
It is definitionally the identity on every underlying sheaf and morphism. -/
def coherentPrincipalRestrictionSquare :
    (coherentAffineEquivalence R).functor ⋙ affinePrincipalRestriction R r ≅
      coherentRestriction (principalOpen R r) ⋙
        (coherentAffineEquivalence (CommRingCat.of (Localization.Away r))).functor :=
  Iso.refl _

/-- Actual restriction on the global coherent categories of two spectra is
the Serre localization by its actual kernel. -/
instance coherentPrincipalRestriction_isLocalization_kernel :
    (coherentRestriction (principalOpen R r)).IsLocalization
      (coherentRestriction (principalOpen R r)).kernel.isoModSerre := by
  let L := affinePrincipalRestriction R r
  let P := L.kernel
  let e := coherentAffineEquivalence R
  let e' := coherentAffineEquivalence (CommRingCat.of (Localization.Away r))
  let square : CatCommSq e.functor (coherentRestriction (principalOpen R r)) L e'.functor :=
    ⟨coherentPrincipalRestrictionSquare R r⟩
  let : CatCommSq e.symm.functor L (coherentRestriction (principalOpen R r)) e'.symm.functor :=
    CatCommSq.hInv e _ _ e' square
  have hinv : (coherentRestriction (principalOpen R r)).kernel.isoModSerre.IsInvertedBy
      (coherentRestriction (principalOpen R r)) := by
    rw [Abelian.isoModSerre_kernel_eq_inverseImage_isomorphisms]
    intro M N f hf
    exact hf
  apply Functor.IsLocalization.of_equivalences L P.isoModSerre
    (coherentRestriction (principalOpen R r))
    (coherentRestriction (principalOpen R r)).kernel.isoModSerre
    e.symm e'.symm ?_ hinv
  have hi : P.isoModSerre.IsInvertedBy
      (e.symm.functor ⋙ coherentRestriction (principalOpen R r)) :=
    (MorphismProperty.IsInvertedBy.iff_of_iso _
      (CatCommSq.iso e.symm.functor L (coherentRestriction (principalOpen R r))
        e'.symm.functor)).2
      (Localization.inverts (L ⋙ e'.symm.functor) P.isoModSerre)
  intro M N f hf
  apply MorphismProperty.le_isoClosure
  rw [Abelian.isoModSerre_kernel_eq_inverseImage_isomorphisms]
  exact hi f hf

/-- Equivalently, it is localization by actual coherent sheaves supported in
the closed complement of the principal open. -/
instance coherentPrincipalRestriction_isLocalization :
    (coherentRestriction (principalOpen R r)).IsLocalization
      (coherentSupportedAway (principalOpen R r)).isoModSerre := by
  have h : (coherentRestriction (principalOpen R r)).kernel.isoModSerre =
      (coherentSupportedAway (principalOpen R r)).isoModSerre := by
    funext M N f
    apply propext
    change ((coherentRestriction (principalOpen R r)).kernel (kernel f) ∧
      (coherentRestriction (principalOpen R r)).kernel (cokernel f)) ↔ _
    rw [coherentRestriction_kernel_eq_support]
    rfl
  rw [← h]
  infer_instance

end Quillen.CoherentScheme
