import Quillen.Scheme.Coherent.Affine.PrincipalLocalization
import Quillen.Scheme.Coherent.Affine.ClosedDevissage
import Quillen.Scheme.Coherent.Affine.Comparison

/-!
# Public lower-universe affine coherent G-theory

These groups use the established `u`-small affine presentation. They are kept
separate from the `u + 1`-small global `Quillen.Scheme.G` until the corresponding
presentation comparison is proved. All maps below retain the original geometric
restriction, supported inclusion and path-space connecting homomorphism.
-/
noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.Scheme.Affine
variable (R : CommRingCat.{u}) [IsNoetherianRing R]

/-- Actual affine coherent G-theory in its established `u`-small presentation. -/
abbrev G (n : ℕ) : Type u := CoherentScheme.AffineG R n

/-- The canonical equivalence induced by affine global sections. -/
abbrev moduleEquiv (n : ℕ) : G R n ≃* CoherentScheme.RingG R n :=
  CoherentScheme.affineGEquiv R n

/-- The forward affine comparison is precisely the existing global-sections map. -/
@[simp] theorem moduleEquiv_toMonoidHom (n : ℕ) :
    (moduleEquiv R n).toMonoidHom = CoherentScheme.affineGToRingG R n := rfl

variable (r : R)

/-- The actual principal-closed supported G-term. -/
abbrev SupportedG (n : ℕ) : Type u := CoherentScheme.PrincipalSupportedG R r n

/-- Geometric restriction from `Spec R` to its principal open. -/
abbrev restrictG (n : ℕ) : G R n →* G (CommRingCat.of (Localization.Away r)) n :=
  CoherentScheme.principalRestrictionGMap R r n

/-- The canonical supported inclusion. -/
abbrev inclusionG (n : ℕ) : SupportedG R r n →* G R n :=
  CoherentScheme.principalInclusionGMap R r n

/-- The connecting homomorphism constructed from the actual path-space boundary. -/
abbrev boundaryG (n : ℕ) :
    G (CommRingCat.of (Localization.Away r)) (n + 1) →* SupportedG R r n :=
  CoherentScheme.principalConnectingHom R r n

/-- The public principal-open map is the original exact restriction K-map. -/
@[simp] theorem restrictG_eq_smallKMap (n : ℕ) :
    restrictG R r n = (CoherentScheme.affinePrincipalRestrictionExact R r).smallKMap n := rfl

/-- Exactness at the ambient affine G-group. -/
theorem inclusion_range_eq_restrict_ker (n : ℕ) :
    (inclusionG R r n).range = (restrictG R r n).ker :=
  (CoherentScheme.principal_localization_longExact R r).1 n

/-- Exactness at the principal-open G-group. -/
theorem restrict_range_eq_boundary_ker (n : ℕ) :
    (restrictG R r (n + 1)).range = (boundaryG R r n).ker :=
  (CoherentScheme.principal_localization_longExact R r).2.1 n

/-- Exactness at the genuine support group. -/
theorem boundary_range_eq_inclusion_ker (n : ℕ) :
    (boundaryG R r n).range = (inclusionG R r n).ker :=
  (CoherentScheme.principal_localization_longExact R r).2.2.1 n

/-- The connective affine sequence ends in a surjection on G₀. -/
theorem restrictG_zero_surjective : Function.Surjective (restrictG R r 0) :=
  CoherentScheme.principal_GZero_surjective R r

end Quillen.Scheme.Affine
