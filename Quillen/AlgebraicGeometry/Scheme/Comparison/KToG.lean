/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.AlgebraicGeometry.Scheme.VectorBundle.Coherent
public import Quillen.AlgebraicGeometry.Scheme.KTheory
public import Quillen.AlgebraicGeometry.Scheme.GTheory
public import Quillen.CategoryTheory.SmallModel.Functoriality

/-!
# The canonical comparison from scheme K-theory to coherent G-theory

Finite locally free sheaves satisfy the affine-local finite quasicoherent
condition on every scheme. On a locally noetherian scheme their actual full
inclusion into coherent sheaves is exact for the ambient short exact
sequences. Its canonical small-model K-map is the comparison from K to G.
The comparison commutes with actual geometric open restriction.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.SchemeSheaf

variable (X : Scheme.{u}) [IsLocallyNoetherian X]

/-- The canonical comparison is the small-model K-map of the actual exact inclusion. -/
def schemeKToG (n : ℕ) : SchemeK X n →* CoherentScheme.G X n :=
  (vectorBundleToCoherentExact X).smallKMap n

@[simp]
theorem schemeKToG_eq_smallKMap (n : ℕ) :
    schemeKToG X n = (vectorBundleToCoherentExact X).smallKMap n := rfl

variable {X} {U : Scheme.{u}} [IsLocallyNoetherian U]
  (j : U ⟶ X) [IsOpenImmersion j]

/-- The canonical K-to-G comparison commutes with actual open restriction. -/
theorem schemeKToG_restrict (n : ℕ) :
    (CoherentScheme.restrictionGMap j n).comp (schemeKToG X n) =
      (schemeKToG U n).comp (schemeKRestrict j n) := by
  change ((CoherentScheme.coherentRestrictionExact j).smallKMap n).comp
      ((vectorBundleToCoherentExact X).smallKMap n) =
    ((vectorBundleToCoherentExact U).smallKMap n).comp
      ((vectorBundleExactRestrict j).smallKMap n)
  rw [← ExactFunctor.smallKMap_comp, ← ExactFunctor.smallKMap_comp]
  exact ExactFunctor.smallKMap_eq_of_natIso (vectorBundleToCoherentRestrictIso j) n

/-- Elementwise naturality of the comparison. -/
theorem schemeKToG_restrict_apply (n : ℕ) (x : SchemeK X n) :
    CoherentScheme.restrictionGMap j n (schemeKToG X n x) =
      schemeKToG U n (schemeKRestrict j n x) :=
  DFunLike.congr_fun (schemeKToG_restrict j n) x

end Quillen.SchemeSheaf

namespace Quillen.Scheme

/-- The canonical comparison from genuine scheme K-theory to coherent G-theory. -/
def KToG (X : AlgebraicGeometry.Scheme.{u}) [IsLocallyNoetherian X] (n : ℕ) :
    K X n →* G X n := SchemeSheaf.schemeKToG X n

@[simp]
theorem KToG_eq_smallKMap (X : AlgebraicGeometry.Scheme.{u})
    [IsLocallyNoetherian X] (n : ℕ) :
    KToG X n = (SchemeSheaf.vectorBundleToCoherentExact X).smallKMap n := rfl

/-- The public comparison is natural for actual open restriction on K and G. -/
theorem KToG_restrict {U X : AlgebraicGeometry.Scheme.{u}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian U]
    (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ) :
    (restrictG j n).comp (KToG X n) = (KToG U n).comp (restrictK j n) :=
  SchemeSheaf.schemeKToG_restrict j n

/-- The pointwise form of the public restriction square. -/
theorem KToG_restrict_apply {U X : AlgebraicGeometry.Scheme.{u}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian U]
    (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ) (x : K X n) :
    restrictG j n (KToG X n x) = KToG U n (restrictK j n x) :=
  DFunLike.congr_fun (KToG_restrict j n) x

end Quillen.Scheme
