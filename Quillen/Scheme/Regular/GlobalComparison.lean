import Quillen.Scheme.Regular.GlobalResolution
import Quillen.Scheme.Regular.KernelClosure
import Quillen.Scheme.Regular.Affine

/-!
# The canonical global regular-scheme K-to-G equivalence

For a quasi-compact regular scheme satisfying the ordinary geometric
resolution property, the genuine vector-bundle inclusion induces an
isomorphism on every nonnegative K-group. All finite-resolution hypotheses
are proved by global coherent syzygies and local projective-dimension bounds.
No finite Krull dimension or global projectivity of vector bundles is used.
-/

noncomputable section
universe u
open AlgebraicGeometry

namespace Quillen.Scheme

variable (X : AlgebraicGeometry.Scheme.{u}) [IsRegular X] [CompactSpace X]
  [HasResolutionProperty X]

/-- The original inclusion-induced comparison is bijective on a regular
quasi-compact scheme with the ordinary resolution property. -/
theorem KToG_regular_resolutionProperty_bijective (n : ℕ) :
    Function.Bijective (KToG X n) :=
  SchemeSheaf.schemeKToG_bijective_of_finite_resolutions X
    SchemeSheaf.coherentResolutionHypothesis_of_regular_resolutionProperty n

/-- The canonical global vector-bundle K-to-G equivalence for a regular
scheme with the resolution property, in every nonnegative degree. -/
def KToGRegularEquiv (n : ℕ) : K X n ≃* G X n :=
  MulEquiv.ofBijective (KToG X n) (KToG_regular_resolutionProperty_bijective X n)

@[simp]
theorem KToGRegularEquiv_toMonoidHom (n : ℕ) :
    (KToGRegularEquiv X n).toMonoidHom = KToG X n := rfl

/-- The global equivalence preserves the original geometric restriction
square, since its forward map is literally the canonical comparison. -/
theorem KToGRegularEquiv_restrict {U X : AlgebraicGeometry.Scheme.{u}}
    [IsRegular X] [CompactSpace X] [HasResolutionProperty X]
    [IsRegular U] [CompactSpace U] [HasResolutionProperty U]
    (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ) (x : K X n) :
    restrictG j n (KToGRegularEquiv X n x) =
      KToGRegularEquiv U n (restrictK j n x) :=
  KToG_restrict_apply j n x

/-- The genuine global theorem specializes to exactly the independently
constructed regular-affine equivalence, not merely an unspecified abstract
isomorphism of the same groups. The affine resolution property is proved. -/
theorem KToGRegularEquiv_spec (R : CommRingCat.{u}) [IsRegularRing R] (n : ℕ) :
    KToGRegularEquiv (Spec R) n = KToGRegularAffineEquiv R n := by
  ext x
  rfl

end Quillen.Scheme
