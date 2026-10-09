import Quillen.Scheme.Coherent.Affine.Restriction
import Quillen.Scheme.Coherent.Affine.Support
import Quillen.GTheory.FiniteModules.Localization.Quotient
import Mathlib.CategoryTheory.Localization.Equivalence

/-!
# Principal-open restriction is the actual coherent Serre localization

The geometric restriction functor is exact. The proved comparison square
with scalar localization transports the universal property, and its kernel
is identified with the actual stalk-support condition.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.CoherentScheme
variable (R : CommRingCat.{u}) [IsNoetherianRing R] (r : R)

instance affinePrincipalRestriction_preservesFiniteLimits :
    PreservesFiniteLimits (affinePrincipalRestriction R r) := by
  have : PreservesFiniteLimits
      (affinePrincipalRestriction R r ⋙ affineCoherentToSheaves (CommRingCat.of (Localization.Away r))) := by
    rw [affinePrincipalRestriction_comp_inclusion]
    infer_instance
  exact preservesFiniteLimits_of_reflects_of_preserves (affinePrincipalRestriction R r)
    (affineCoherentToSheaves (CommRingCat.of (Localization.Away r)))

instance affinePrincipalRestriction_preservesFiniteColimits :
    PreservesFiniteColimits (affinePrincipalRestriction R r) := by
  have : PreservesFiniteColimits
      (affinePrincipalRestriction R r ⋙ affineCoherentToSheaves (CommRingCat.of (Localization.Away r))) := by
    rw [affinePrincipalRestriction_comp_inclusion]
    infer_instance
  exact preservesFiniteColimits_of_reflects_of_preserves (affinePrincipalRestriction R r)
    (affineCoherentToSheaves (CommRingCat.of (Localization.Away r)))

instance affinePrincipalRestriction_additive : (affinePrincipalRestriction R r).Additive := by
  let := preservesBinaryBiproducts_of_preservesBinaryProducts (affinePrincipalRestriction R r)
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- The exact functor whose underlying functor is actual geometric restriction. -/
def affinePrincipalRestrictionExact :
    ExactFunctor (affineCoherentExactStructure R)
      (affineCoherentExactStructure (CommRingCat.of (Localization.Away r))) where
  toFunctor := affinePrincipalRestriction R r
  map_conflation _ h := h.map_of_exact _

/-- The kernel is exactly the geometric support subcategory already defined
using actual restriction, equivalently stalk support in the open complement. -/
theorem principalRestriction_kernel_eq_support :
    (affinePrincipalRestriction R r).kernel = affineSupportedAway R (principalOpen R r) := by
  funext M
  apply propext
  change IsZero ((affinePrincipalRestriction R r).obj M) ↔
    IsZero ((affineCoherentToSheaves (CommRingCat.of (Localization.Away r))).obj
      ((affinePrincipalRestriction R r).obj M))
  exact ⟨Functor.map_isZero _, fun h => IsZero.of_full_of_faithful_of_isZero _ _ h⟩

/-- The actual coherent restriction functor has the Serre localization
universal property for its actual kernel. -/
instance affinePrincipalRestriction_isLocalization_kernel :
    (affinePrincipalRestriction R r).IsLocalization
      (affinePrincipalRestriction R r).kernel.isoModSerre := by
  let L := FiniteModuleLocalization.functor (Submonoid.powers r)
  let P := FiniteModuleLocalization.torsion (Submonoid.powers r)
  let e := affineCoherentEquivalence R
  let e' := affineCoherentEquivalence (CommRingCat.of (Localization.Away r))
  let square : CatCommSq e.functor (affinePrincipalRestriction R r) L e'.functor :=
    ⟨affinePrincipalRestrictionSquare R r⟩
  let : CatCommSq e.symm.functor L (affinePrincipalRestriction R r) e'.symm.functor :=
    CatCommSq.hInv e _ _ e' square
  have hinv : (affinePrincipalRestriction R r).kernel.isoModSerre.IsInvertedBy
      (affinePrincipalRestriction R r) := by
    rw [Abelian.isoModSerre_kernel_eq_inverseImage_isomorphisms]
    intro M N f hf
    exact hf
  apply Functor.IsLocalization.of_equivalences L P.isoModSerre
    (affinePrincipalRestriction R r) (affinePrincipalRestriction R r).kernel.isoModSerre
    e.symm e'.symm ?_ hinv
  have hi : P.isoModSerre.IsInvertedBy (e.symm.functor ⋙ affinePrincipalRestriction R r) :=
    (MorphismProperty.IsInvertedBy.iff_of_iso _
      (CatCommSq.iso e.symm.functor L (affinePrincipalRestriction R r) e'.symm.functor)).2
        (Localization.inverts (L ⋙ e'.symm.functor) P.isoModSerre)
  intro M N f hf
  apply MorphismProperty.le_isoClosure
  rw [Abelian.isoModSerre_kernel_eq_inverseImage_isomorphisms]
  exact hi f hf

/-- Principal-open coherent restriction is localization by sheaves whose
ordinary support lies in the closed complement. -/
instance affinePrincipalRestriction_isLocalization :
    (affinePrincipalRestriction R r).IsLocalization
      (affineSupportedAway R (principalOpen R r)).isoModSerre := by
  have h : (affinePrincipalRestriction R r).kernel.isoModSerre =
      (affineSupportedAway R (principalOpen R r)).isoModSerre := by
    funext M N f
    apply propext
    change ((affinePrincipalRestriction R r).kernel (kernel f) ∧
      (affinePrincipalRestriction R r).kernel (cokernel f)) ↔ _
    rw [principalRestriction_kernel_eq_support]
    rfl
  rw [← h]
  infer_instance

end Quillen.CoherentScheme
