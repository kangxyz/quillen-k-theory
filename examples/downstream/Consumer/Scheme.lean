/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.AlgebraicGeometry.Scheme

/-!
# Scheme K-theory and G-theory interface examples

Uses the global groups and their geometric restriction maps, alongside the
separately named affine G-theory presentation. The examples record principal
and arbitrary-open exactness, naturality of K-to-G, and the geometric closed
pushforward in the principal closed/open sequence.
-/

@[expose] public section

open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Consumer

-- Upper-universe global K/G groups and canonical geometric restriction maps.
abbrev GlobalK (X : AlgebraicGeometry.Scheme.{u}) (n : ℕ) : Type (u + 1) :=
  AlgebraicGeometry.Scheme.K X n
abbrev GlobalG (X : AlgebraicGeometry.Scheme.{u}) [IsLocallyNoetherian X] (n : ℕ) :
    Type (u + 1) := AlgebraicGeometry.Scheme.G X n

theorem geometric_K_map {U X : AlgebraicGeometry.Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ)
  :
    AlgebraicGeometry.Scheme.restrictK j n =
      (AlgebraicGeometry.Scheme.Modules.vectorBundleExactRestrict j).smallKMap n :=
  AlgebraicGeometry.Scheme.restrictK_eq_smallKMap j n

theorem geometric_G_map {U X : AlgebraicGeometry.Scheme.{u}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian U]
    (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ) :
    AlgebraicGeometry.Scheme.restrictG j n =
      (AlgebraicGeometry.Scheme.Modules.Coherent.coherentRestrictionExact j).smallKMap n
      :=
  AlgebraicGeometry.Scheme.restrictG_eq_smallKMap j n

-- The separately named lower-universe affine presentation and its proved LES.
abbrev AffineG (R : CommRingCat.{u}) [IsNoetherianRing R] (n : ℕ) :
    Type u := AlgebraicGeometry.Scheme.Affine.G R n

theorem affine_principal_exact (R : CommRingCat.{u}) [IsNoetherianRing R] (r : R) (n : ℕ) :
    (AlgebraicGeometry.Scheme.Affine.inclusionG R r n).range =
      (AlgebraicGeometry.Scheme.Affine.restrictG R r n).ker :=
  AlgebraicGeometry.Scheme.Affine.inclusion_range_eq_restrict_ker R r n
-- The same principal-open sequence directly on the public upper-universe G.
theorem global_principal_exact (R : CommRingCat.{u}) [IsNoetherianRing R] (r : R) (n : ℕ) :
    (AlgebraicGeometry.Scheme.Principal.inclusionG R r n).range =
      (AlgebraicGeometry.Scheme.restrictG
        (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r) n).ker :=
  AlgebraicGeometry.Scheme.Principal.inclusion_range_eq_restrict_ker R r n

-- The actual vector-bundle inclusion is natural for geometric restriction.
theorem K_to_G_naturality {U X : AlgebraicGeometry.Scheme.{u}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian U]
    (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ) :
    (AlgebraicGeometry.Scheme.restrictG j n).comp (AlgebraicGeometry.Scheme.KToG X n) =
      (AlgebraicGeometry.Scheme.KToG U n).comp (AlgebraicGeometry.Scheme.restrictK j n) :=
  AlgebraicGeometry.Scheme.KToG_restrict j n

-- Arbitrary opens of noetherian schemes, with the original geometric arrows.
theorem noetherian_open_exact {U X : AlgebraicGeometry.Scheme.{u}}
    [IsNoetherian X] [IsLocallyNoetherian U]
    (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ) :
    (AlgebraicGeometry.Scheme.inclusionG j n).range = (AlgebraicGeometry.Scheme.restrictG j n).ker
      :=
  AlgebraicGeometry.Scheme.inclusion_range_eq_restrict_ker j n

-- The closed arrow is actual sheaf pushforward, not just a module alias.
theorem principal_closed_geometric_exact (R : CommRingCat.{u}) [IsNoetherianRing R]
    (f : R) (n : ℕ) :
    (AlgebraicGeometry.Scheme.PrincipalClosed.pushforwardG R f n).range =
      (AlgebraicGeometry.Scheme.restrictG
        (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R f) n).ker :=
  AlgebraicGeometry.Scheme.PrincipalClosed.pushforward_range_eq_restrict_ker R f n

end Consumer
