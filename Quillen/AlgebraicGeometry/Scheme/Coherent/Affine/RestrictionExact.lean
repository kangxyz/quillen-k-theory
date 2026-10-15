/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FiniteTypeCategory
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FiniteTypeSupport
public import Aglib.AlgebraicGeometry.Modules.Coherent.Affine.RestrictionExact
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FiniteTypeRestriction
public import Quillen.AlgebraicGeometry.Scheme.Coherent.Affine.Support
public import Quillen.GTheory.FiniteModules.Localization.Quotient
public import Mathlib.CategoryTheory.Localization.Equivalence

/-!
# Principal-open restriction is the actual coherent Serre localization

The geometric restriction functor is exact. The proved comparison square
with scalar localization transports the universal property, and its kernel
is identified with the actual stalk-support condition.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Coherent


open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open Quillen





noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules.Coherent
variable (R : CommRingCat.{u}) [IsNoetherianRing R] (r : R)

/-- The actual coherent restriction functor has the Serre localization
universal property for its actual kernel. -/
instance affinePrincipalRestriction_isLocalization_kernel :
    (affinePrincipalRestriction R r).IsLocalization
      (affinePrincipalRestriction R r).kernel.isoModSerre := by
  let L := ModuleCat.FiniteLocalization.functor (Submonoid.powers r)
  let P := ModuleCat.FiniteLocalization.torsion (Submonoid.powers r)
  let e := affineFiniteTypeModuleEquivalence R
  let e' := affineFiniteTypeModuleEquivalence (CommRingCat.of (Localization.Away r))
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

end AlgebraicGeometry.Scheme.Modules.Coherent
