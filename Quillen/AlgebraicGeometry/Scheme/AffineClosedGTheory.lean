/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.AlgebraicGeometry.Scheme.GTheory
public import Quillen.AlgebraicGeometry.Scheme.Coherent.ClosedImmersion.IdealLocalization

/-! Public affine closed–open G-localization for an arbitrary ideal. -/
@[expose] public section

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
namespace Quillen.Scheme.AffineClosed
variable (R : CommRingCat.{u}) [IsNoetherianRing R] (I : Ideal R)

/-- The actual affine closed subscheme Spec(R/I). -/
abbrev closedScheme := Spec (CoherentScheme.ClosedImmersion.Ideal.closedRing R I)

/-- The actual open complement of V(I), which need not be affine. -/
abbrev openScheme := (CoherentScheme.ClosedImmersion.Ideal.openComplement R I).toScheme

/-- Its canonical open immersion into Spec R. -/
abbrev openMap := CoherentScheme.ClosedImmersion.Ideal.openMap R I

/-- The canonical map of actual closed-immersion sheaf pushforward. -/
abbrev pushforwardG (n : ℕ) : G (closedScheme R I) n →* G (Spec R) n :=
  CoherentScheme.ClosedImmersion.Ideal.coherentPushforwardGMap R I n

/-- Dévissage identifies G of the actual closed scheme with supported G. -/
abbrev supportedGEquiv (n : ℕ) : G (closedScheme R I) n ≃* SupportedG (openMap R I) n :=
  CoherentScheme.ClosedImmersion.Ideal.closedSupportedGEquiv R I n

/-- The actual geometric localization boundary. -/
abbrev boundaryG (n : ℕ) : G (openScheme R I) (n + 1) →* G (closedScheme R I) n :=
  CoherentScheme.ClosedImmersion.Ideal.closedConnectingHom R I n

/-- Exactness at the ambient affine scheme. -/
theorem pushforward_range_eq_restrict_ker (n : ℕ) :
    (pushforwardG R I n).range = (restrictG (openMap R I) n).ker :=
  CoherentScheme.ClosedImmersion.Ideal.pushforward_range_eq_restriction_ker R I n

/-- Exactness at the arbitrary open complement. -/
theorem restrict_range_eq_boundary_ker (n : ℕ) :
    (restrictG (openMap R I) (n + 1)).range = (boundaryG R I n).ker :=
  CoherentScheme.ClosedImmersion.Ideal.restriction_range_eq_closedConnecting_ker R I n

/-- Exactness at the actual affine closed subscheme. -/
theorem boundary_range_eq_pushforward_ker (n : ℕ) :
    (boundaryG R I n).range = (pushforwardG R I n).ker :=
  CoherentScheme.ClosedImmersion.Ideal.closedConnecting_range_eq_pushforward_ker R I n

/-- The connective localization sequence terminates surjectively at G₀(U). -/
theorem restrictG_zero_surjective : Function.Surjective (restrictG (openMap R I) 0) :=
  (CoherentScheme.ClosedImmersion.Ideal.affine_closed_open_longExact R I).2.2.2
end Quillen.Scheme.AffineClosed
