/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.AlgebraicGeometry.Scheme.Regular

/-!
# Regular K-to-G comparison examples

Uses the canonical scheme K-to-G map for principal ideal domains and regular
affine rings, including the dimension-at-most-one specialization. The nonaffine
examples retain compactness and the geometric resolution property, identify
canonical forward maps, and compare the global and affine equivalences.
-/

@[expose] public section
noncomputable section
open AlgebraicGeometry
universe u
namespace Consumer
variable (R : CommRingCat.{u}) [IsDomain R] [IsPrincipalIdealRing R]

/-- A genuine regular affine family with no caller-supplied resolution data. -/
theorem pid_K_to_G_bijective (n : ℕ) :
    Function.Bijective (Quillen.Scheme.KToG (Spec R) n) :=
  Quillen.Scheme.KToG_pid_bijective R n

/-- The equivalence uses the original canonical geometric comparison map. -/
theorem pid_K_to_G_forward (n : ℕ) :
    (Quillen.Scheme.KToGPIDEquiv R n).toMonoidHom = Quillen.Scheme.KToG (Spec R) n := rfl

/-- Actual regularity and dimension at most one suffice; no supplied resolutions. -/
theorem regular_dimension_one_comparison (S : CommRingCat.{u}) [IsRegularRing S]
    (h : ringKrullDim S ≤ 1) (n : ℕ) :
    Function.Bijective (Quillen.Scheme.KToG (Spec S) n) :=
  Quillen.Scheme.KToG_regular_dimension_le_one_bijective S h n


/-- Arbitrary regular affine rings require no common dimension bound. -/
theorem regular_affine_comparison (S : CommRingCat.{u}) [IsRegularRing S] (n : ℕ) :
    Function.Bijective (Quillen.Scheme.KToG (Spec S) n) :=
  Quillen.Scheme.KToG_regular_affine_bijective S n

/-- The unrestricted affine equivalence is the original canonical map. -/
theorem regular_affine_forward (S : CommRingCat.{u}) [IsRegularRing S] (n : ℕ) :
    (Quillen.Scheme.KToGRegularAffineEquiv S n).toMonoidHom =
      Quillen.Scheme.KToG (Spec S) n := rfl
/-- The nonaffine theorem assumes the ordinary geometric resolution property. -/
theorem regular_scheme_comparison (X : Scheme.{u}) [Quillen.Scheme.IsRegular X]
    [CompactSpace X] [Quillen.Scheme.HasResolutionProperty X] (n : ℕ) :
    Function.Bijective (Quillen.Scheme.KToG X n) :=
  Quillen.Scheme.KToG_regular_resolutionProperty_bijective X n

/-- The original canonical comparison remains the forward map. -/
theorem regular_scheme_forward (X : Scheme.{u}) [Quillen.Scheme.IsRegular X]
    [CompactSpace X] [Quillen.Scheme.HasResolutionProperty X] (n : ℕ) :
    (Quillen.Scheme.KToGRegularEquiv X n).toMonoidHom = Quillen.Scheme.KToG X n := rfl

/-- The global and independently proved affine comparisons agree. -/
theorem regular_scheme_affine_agreement (S : CommRingCat.{u}) [IsRegularRing S] (n : ℕ) :
    Quillen.Scheme.KToGRegularEquiv (Spec S) n = Quillen.Scheme.KToGRegularAffineEquiv S n :=
  Quillen.Scheme.KToGRegularEquiv_spec S n
end Consumer
