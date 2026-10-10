/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.AlgebraicGeometry.Scheme.AffineClosedGTheory

/-!
# Affine closed localization examples

Uses the public G-theory closed/open sequence for an arbitrary ideal in a
noetherian ring. The examples identify the pushforward range with the open
restriction kernel and record surjectivity of the degree-zero restriction.
-/

@[expose] public section
noncomputable section
open AlgebraicGeometry
namespace Consumer
universe u
variable (R : CommRingCat.{u}) [IsNoetherianRing R] (I : Ideal R)

/-- The public arbitrary-ideal closed/open interface uses genuine scheme G. -/
theorem affine_closed_exact (n : ℕ) :
    (Quillen.Scheme.AffineClosed.pushforwardG R I n).range =
      (Quillen.Scheme.restrictG (Quillen.Scheme.AffineClosed.openMap R I) n).ker :=
  Quillen.Scheme.AffineClosed.pushforward_range_eq_restrict_ker R I n

/-- The open complement need not be affine, and the G₀ tail is surjective. -/
theorem affine_closed_tail : Function.Surjective
    (Quillen.Scheme.restrictG (Quillen.Scheme.AffineClosed.openMap R I) 0) :=
  Quillen.Scheme.AffineClosed.restrictG_zero_surjective R I
end Consumer
