/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Algebra.RegularLocal.GlobalProjectiveDimension
public import Quillen.AlgebraicGeometry.Scheme.Regular.GeneralComparison

/-!
# The canonical K-to-G equivalence on every regular affine scheme

The sole ring-theoretic assumption is mathlib's actual `IsRegularRing`.
Finite projective resolutions are derived from regular-local parameter
induction and an objectwise compactness argument. No finite Krull-dimension
bound, finite-resolution hypothesis or K-equivalence is assumed.
-/
@[expose] public section

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.SchemeSheaf

/-- Every actual coherent sheaf on a regular affine scheme has a genuine
finite locally free admissible resolution, with an object-dependent length. -/
theorem coherentResolutionHypothesis_of_regular (R : CommRingCat.{u}) [IsRegularRing R] :
    (CoherentScheme.coherentExactStructure (Spec R)).ResolutionHypothesis
      (coherentVectorBundle (Spec R)) :=
  coherentResolutionHypothesis_of_finite_projectiveDimension R
    (fun M => CoherentScheme.projectiveDimension_ne_top_of_regular R M.obj)

end Quillen.SchemeSheaf

namespace Quillen.Scheme

/-- On the spectrum of any regular Noetherian ring, the original canonical
inclusion-induced K-to-G map is bijective in every nonnegative degree. -/
theorem KToG_regular_affine_bijective (R : CommRingCat.{u}) [IsRegularRing R] (n : ℕ) :
    Function.Bijective (KToG (Spec R) n) :=
  SchemeSheaf.schemeKToG_bijective_of_finite_resolutions (Spec R)
    (SchemeSheaf.coherentResolutionHypothesis_of_regular R) n

/-- The actual canonical regular-affine K-to-G equivalence. -/
def KToGRegularAffineEquiv (R : CommRingCat.{u}) [IsRegularRing R] (n : ℕ) :
    K (Spec R) n ≃* G (Spec R) n :=
  MulEquiv.ofBijective (KToG (Spec R) n) (KToG_regular_affine_bijective R n)

/-- The monoid-hom coercion is the canonical forward map. -/
@[simp] theorem KToGRegularAffineEquiv_coe (R : CommRingCat.{u}) [IsRegularRing R] (n : ℕ) :
    ↑(KToGRegularAffineEquiv R n) = KToG (Spec R) n := rfl

/-- The regular-affine equivalence retains the original geometric open-
restriction naturality because its forward map is the actual canonical map. -/
theorem KToGRegularAffineEquiv_restrict {R S : CommRingCat.{u}}
    [IsRegularRing R] [IsRegularRing S] (j : Spec S ⟶ Spec R) [IsOpenImmersion j]
    (n : ℕ) (x : K (Spec R) n) :
    restrictG j n (KToGRegularAffineEquiv R n x) =
      KToGRegularAffineEquiv S n (restrictK j n x) :=
  KToG_restrict_apply j n x

end Quillen.Scheme
