/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.FinitePresentation.Transport
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Restriction
public import Quillen.AlgebraicGeometry.Scheme.VectorBundle.KTheory

/-!
# Actual open restriction of vector bundles

The local bases are transported by the same continuous-site pushforward that
implements geometric open restriction. Their index types are unchanged, so
both freeness and finiteness survive. The induced exact functor and K-map use
the underlying geometric restriction, not a surrogate module functor.
-/
@[expose] public section
open Quillen
open Quillen.SchemeSheaf


-- Transitional names share Aglib declarations and canonical instances.
noncomputable section
namespace Quillen.SchemeSheaf
export AlgebraicGeometry.Scheme.Modules
  (finiteLocallyFree_restrict localBasisPushforward_preservesColimits pushforwardLocalBasis
  pushforwardLocalBasis_isFiniteType pushforwardLocalBasis_isLocallyFreeData
  vectorBundleExactRestrict vectorBundleRestrict vectorBundleRestrict_additive
  vectorBundleRestrict_comp_forget)
end Quillen.SchemeSheaf

end




noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u w w' t t'
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules

section General
variable {C : Type w} [Category.{w'} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}
  {D : Type t} [Category.{t'} D] {K : GrothendieckTopology D}
  {S : Sheaf K RingCat.{u}}
  [∀ U, HasSheafify (J.over U) AddCommGrpCat.{u}]
  [∀ U, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ U, HasSheafify (K.over U) AddCommGrpCat.{u}]
  [∀ U, (K.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  (G : D ⥤ C) [G.IsContinuous K J] [G.IsCocontinuous K J]
  (φ : S ⟶ (G.sheafPushforwardContinuous RingCat.{u} K J).obj R)
  (η : (SheafOfModules.pushforward φ).obj (SheafOfModules.unit R) ≅ SheafOfModules.unit S)
  [G.IsLeftAdjoint] [IsIso φ]
  [∀ U, (Over.post (X := U) G).IsContinuous (K.over U) (J.over (G.obj U))]
  [HasPullbacks C] [HasPullbacks D]

end General

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The canonical contravariant open-restriction map on genuine scheme
K-groups, induced by actual restriction of vector bundles. -/
def schemeKRestrict (n : ℕ) : SchemeK X n →* SchemeK U n :=
  (vectorBundleExactRestrict j).smallKMap n

end AlgebraicGeometry.Scheme.Modules
