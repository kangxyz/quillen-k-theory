/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Aglib.AlgebraicGeometry.Modules.LocallyFree.Resolution.RegularAffine

public import Quillen.Aglib.RingTheory.RegularLocalRing.GlobalProjectiveDimension
public import Quillen.AlgebraicGeometry.Scheme.Regular.GeneralComparison

/-!
# The canonical K-to-G equivalence on every regular affine scheme

The sole ring-theoretic assumption is mathlib's actual `IsRegularRing`.
Finite projective resolutions are derived from regular-local parameter
induction and an objectwise compactness argument. No finite Krull-dimension
bound, finite-resolution hypothesis or K-equivalence is assumed.
-/
@[expose] public section

open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open Quillen


noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme

/-- On the spectrum of any regular Noetherian ring, the original canonical
inclusion-induced K-to-G map is bijective in every nonnegative degree. -/
theorem KToG_regular_affine_bijective (R : CommRingCat.{u}) [IsRegularRing R] (n : ℕ) :
    Function.Bijective (KToG (Spec R) n) :=
  AlgebraicGeometry.Scheme.Modules.schemeKToG_bijective_of_finite_resolutions (Spec R)
    (AlgebraicGeometry.Scheme.Modules.coherentResolutionHypothesis_of_regular R) n

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

end AlgebraicGeometry.Scheme
