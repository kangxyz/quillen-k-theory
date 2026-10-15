/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.AlgebraicGeometry.Scheme.Coherent.Affine.Comparison
public import Quillen.AlgebraicGeometry.Scheme.Coherent.Affine.RestrictionExact
public import Quillen.AlgebraicGeometry.Scheme.Coherent.Restriction

/-!
# Principal restriction of the global coherent category

The identity-on-sheaves affine comparison intertwines actual global coherent
restriction and the previously constructed actual affine restriction. Its
proved equivalences transport the Serre-localization universal property.
-/
@[expose] public section

open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open Quillen
open Quillen.CoherentScheme



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules.Coherent

variable (R : CommRingCat.{u}) [IsNoetherianRing R] (r : R)

/-- The global/affine comparison square for actual principal-open restriction.
It is definitionally the identity on every underlying sheaf and morphism. -/
def coherentPrincipalRestrictionSquare :
    (finiteTypeSheavesAffineEquivalence R).functor ⋙ affinePrincipalRestriction R r ≅
      finiteTypeSheavesRestriction (principalOpen R r) ⋙
        (finiteTypeSheavesAffineEquivalence (CommRingCat.of (Localization.Away r))).functor :=
  Iso.refl _

/-- Actual restriction on the global coherent categories of two spectra is
the Serre localization by its actual kernel. -/
instance coherentPrincipalRestriction_isLocalization_kernel :
    (finiteTypeSheavesRestriction (principalOpen R r)).IsLocalization
      (finiteTypeSheavesRestriction (principalOpen R r)).kernel.isoModSerre := by
  let L := affinePrincipalRestriction R r
  let P := L.kernel
  let e := finiteTypeSheavesAffineEquivalence R
  let e' := finiteTypeSheavesAffineEquivalence (CommRingCat.of (Localization.Away r))
  let square : CatCommSq e.functor (finiteTypeSheavesRestriction (principalOpen R r)) L e'.functor
    :=
    ⟨coherentPrincipalRestrictionSquare R r⟩
  let : CatCommSq e.symm.functor L (finiteTypeSheavesRestriction (principalOpen R r))
    e'.symm.functor :=
    CatCommSq.hInv e _ _ e' square
  have hinv : (finiteTypeSheavesRestriction (principalOpen R r)).kernel.isoModSerre.IsInvertedBy
      (finiteTypeSheavesRestriction (principalOpen R r)) := by
    rw [Abelian.isoModSerre_kernel_eq_inverseImage_isomorphisms]
    intro M N f hf
    exact hf
  apply Functor.IsLocalization.of_equivalences L P.isoModSerre
    (finiteTypeSheavesRestriction (principalOpen R r))
    (finiteTypeSheavesRestriction (principalOpen R r)).kernel.isoModSerre
    e.symm e'.symm ?_ hinv
  have hi : P.isoModSerre.IsInvertedBy
      (e.symm.functor ⋙ finiteTypeSheavesRestriction (principalOpen R r)) :=
    (MorphismProperty.IsInvertedBy.iff_of_iso _
      (CatCommSq.iso e.symm.functor L (finiteTypeSheavesRestriction (principalOpen R r))
        e'.symm.functor)).2
      (Localization.inverts (L ⋙ e'.symm.functor) P.isoModSerre)
  intro M N f hf
  apply MorphismProperty.le_isoClosure
  rw [Abelian.isoModSerre_kernel_eq_inverseImage_isomorphisms]
  exact hi f hf

/-- Equivalently, it is localization by actual coherent sheaves supported in
the closed complement of the principal open. -/
instance coherentPrincipalRestriction_isLocalization :
    (finiteTypeSheavesRestriction (principalOpen R r)).IsLocalization
      (finiteTypeSheavesSupportedAway (principalOpen R r)).isoModSerre := by
  have h : (finiteTypeSheavesRestriction (principalOpen R r)).kernel.isoModSerre =
      (finiteTypeSheavesSupportedAway (principalOpen R r)).isoModSerre := by
    funext M N f
    apply propext
    change ((finiteTypeSheavesRestriction (principalOpen R r)).kernel (kernel f) ∧
      (finiteTypeSheavesRestriction (principalOpen R r)).kernel (cokernel f)) ↔ _
    rw [finiteTypeSheavesRestriction_kernel_eq_support]
    rfl
  rw [← h]
  infer_instance

end AlgebraicGeometry.Scheme.Modules.Coherent
