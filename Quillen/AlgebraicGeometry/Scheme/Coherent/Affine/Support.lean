/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.AlgebraicGeometry.Scheme.Coherent.Affine.GTheory
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.AffineSupport

/-!
# Actual supported coherent sheaves on a noetherian affine scheme

The support category is the kernel of actual open restriction, applied to
actual coherent sheaves. Its Serre property is proved from exactness of the
inclusion and restriction functors. Its objects have ordinary closed stalk
support, and vanishing on the open is equivalent to support in its complement.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.CoherentScheme
variable (R : CommRingCat.{u}) [IsNoetherianRing R]

omit [IsNoetherianRing R] in
/-- The ordinary stalk support of an affine finite-type quasicoherent sheaf is closed. -/
theorem isClosed_support (M : AffineFiniteType R) :
    IsClosed (SchemeSheaf.support ((affineFiniteTypeToModules R).obj M)) :=
  SchemeSheaf.isClosed_support_of_finite_globalSections _

variable {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- Finite-type quasicoherent sheaves supported outside the actual open immersion. -/
def affineSupportedAway : ObjectProperty (AffineFiniteType R) :=
  (SchemeSheaf.supportedAway j).inverseImage (affineFiniteTypeToModules R)

omit [IsNoetherianRing R] in
@[simp]
theorem affineSupportedAway_iff (M : AffineFiniteType R) :
    affineSupportedAway R j M ↔
      IsZero ((Scheme.Modules.restrictFunctor j).obj ((affineFiniteTypeToModules R).obj M)) :=
  Iff.rfl

/-- The support property is a genuine Serre property in coherent sheaves. -/
instance affineSupportedAway_isSerreClass : (affineSupportedAway R j).IsSerreClass := by
  change ((SchemeSheaf.supportedAway j).inverseImage (affineFiniteTypeToModules R)).IsSerreClass
  infer_instance

omit [IsNoetherianRing R] in
/-- Vanishing on the open is equivalent to disjointness of stalk support and
its image. -/
theorem affineSupportedAway_iff_support_disjoint (M : AffineFiniteType R) :
    affineSupportedAway R j M ↔
      Disjoint (SchemeSheaf.support ((affineFiniteTypeToModules R).obj M)) (Set.range j) :=
  SchemeSheaf.supportedAway_iff_support_disjoint j _

omit [IsNoetherianRing R] in
/-- Equivalently, ordinary stalk support is contained in the open complement. -/
theorem affineSupportedAway_iff_support_subset (M : AffineFiniteType R) :
    affineSupportedAway R j M ↔
      SchemeSheaf.support ((affineFiniteTypeToModules R).obj M) ⊆ (Set.range j)ᶜ := by
  rw [affineSupportedAway_iff_support_disjoint]
  exact Set.disjoint_left

/-- The full abelian category of actual supported coherent sheaves. -/
abbrev SupportedAffineFiniteType := (affineSupportedAway R j).FullSubcategory

instance instAbelianSupportedAffineCoherent : Abelian (SupportedAffineFiniteType R j) :=
  inferInstance

instance supportedAffineCoherent_essentiallySmall :
    EssentiallySmall.{u} (SupportedAffineFiniteType R j) :=
  essentiallySmall_of_fully_faithful (affineSupportedAway R j).ι

/-- Its standard abelian exact structure. -/
def supportedAffineCoherentExactStructure : ExactStructure (SupportedAffineFiniteType R j) :=
  abelianExactStructure _

/-- G-theory with support, formed from the actual supported coherent category. -/
abbrev SupportedAffineG (n : ℕ) : Type u :=
  CategoryTheory.ExactCategory.ExactStructure.SmallK.{u} (supportedAffineCoherentExactStructure R j)
    n

end Quillen.CoherentScheme
