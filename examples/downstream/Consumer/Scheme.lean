import Quillen.Scheme
noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Consumer

-- Upper-universe global K/G groups and canonical geometric restriction maps.
abbrev GlobalK (X : AlgebraicGeometry.Scheme.{u}) (n : ℕ) : Type (u + 1) := Quillen.Scheme.K X n
abbrev GlobalG (X : AlgebraicGeometry.Scheme.{u}) [IsLocallyNoetherian X] (n : ℕ) :
    Type (u + 1) := Quillen.Scheme.G X n

theorem geometric_K_map {U X : AlgebraicGeometry.Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ) :
    Quillen.Scheme.restrictK j n = (Quillen.SchemeSheaf.vectorBundleExactRestrict j).smallKMap n :=
  Quillen.Scheme.restrictK_eq_smallKMap j n

theorem geometric_G_map {U X : AlgebraicGeometry.Scheme.{u}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian U]
    (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ) :
    Quillen.Scheme.restrictG j n = (Quillen.CoherentScheme.coherentRestrictionExact j).smallKMap n :=
  Quillen.Scheme.restrictG_eq_smallKMap j n

-- The separately named lower-universe affine presentation and its proved LES.
abbrev AffineG (R : CommRingCat.{u}) [IsNoetherianRing R] (n : ℕ) :
    Type u := Quillen.Scheme.Affine.G R n

theorem affine_principal_exact (R : CommRingCat.{u}) [IsNoetherianRing R] (r : R) (n : ℕ) :
    (Quillen.Scheme.Affine.inclusionG R r n).range =
      (Quillen.Scheme.Affine.restrictG R r n).ker :=
  Quillen.Scheme.Affine.inclusion_range_eq_restrict_ker R r n
-- The same principal-open sequence directly on the public upper-universe G.
theorem global_principal_exact (R : CommRingCat.{u}) [IsNoetherianRing R] (r : R) (n : ℕ) :
    (Quillen.Scheme.Principal.inclusionG R r n).range =
      (Quillen.Scheme.restrictG (Quillen.CoherentScheme.principalOpen R r) n).ker :=
  Quillen.Scheme.Principal.inclusion_range_eq_restrict_ker R r n

-- The actual vector-bundle inclusion is natural for geometric restriction.
theorem K_to_G_naturality {U X : AlgebraicGeometry.Scheme.{u}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian U]
    (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ) :
    (Quillen.Scheme.restrictG j n).comp (Quillen.Scheme.KToG X n) =
      (Quillen.Scheme.KToG U n).comp (Quillen.Scheme.restrictK j n) :=
  Quillen.Scheme.KToG_restrict j n

-- Arbitrary opens of noetherian schemes, with the original geometric arrows.
theorem noetherian_open_exact {U X : AlgebraicGeometry.Scheme.{u}}
    [IsNoetherian X] [IsLocallyNoetherian U]
    (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ) :
    (Quillen.Scheme.inclusionG j n).range = (Quillen.Scheme.restrictG j n).ker :=
  Quillen.Scheme.inclusion_range_eq_restrict_ker j n

-- The closed arrow is actual sheaf pushforward, not just a module alias.
theorem principal_closed_geometric_exact (R : CommRingCat.{u}) [IsNoetherianRing R]
    (f : R) (n : ℕ) :
    (Quillen.Scheme.PrincipalClosed.pushforwardG R f n).range =
      (Quillen.Scheme.restrictG (Quillen.CoherentScheme.principalOpen R f) n).ker :=
  Quillen.Scheme.PrincipalClosed.pushforward_range_eq_restrict_ker R f n

end Consumer
