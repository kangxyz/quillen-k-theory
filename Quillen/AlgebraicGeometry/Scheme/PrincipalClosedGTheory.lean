/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.AlgebraicGeometry.Scheme.GTheory
public import Quillen.AlgebraicGeometry.Scheme.Coherent.ClosedImmersion.Localization

/-! Public principal closed–open G-localization with actual geometric pushforward. -/
@[expose] public section

open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

open AlgebraicGeometry.Scheme
open Quillen


noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.PrincipalClosed
variable (R : CommRingCat.{u}) [IsNoetherianRing R] (f : R)

/-- The actual principal closed subscheme Spec(R/(f)). -/
abbrev closedScheme := Spec
  (AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.ClosedImmersion.principalRing R f)

/-- The canonical G-map of actual closed sheaf pushforward. -/
abbrev pushforwardG (n : ℕ) : G (closedScheme R f) n →* G (Spec R) n :=
  AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.ClosedImmersion.coherentPushforwardGMap R f
    n

/-- The geometric localization boundary with its closed-scheme target. -/
abbrev boundaryG (n : ℕ) :
    G (Spec (CommRingCat.of (Localization.Away f))) (n + 1) →* G (closedScheme R f) n :=
  AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.ClosedImmersion.closedConnectingHom R f n

/-- Exactness at the ambient scheme, with actual i_* and j*. -/
theorem pushforward_range_eq_restrict_ker (n : ℕ) :
    (pushforwardG R f n).range = (restrictG
      (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R f) n).ker :=
  Modules.Coherent.Pushforward.ClosedImmersion.pushforward_range_eq_restriction_ker R f n

/-- Exactness at the principal open. -/
theorem restrict_range_eq_boundary_ker (n : ℕ) :
    (restrictG (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R f) (n + 1)).range =
      (boundaryG R f n).ker :=
  Modules.Coherent.Pushforward.ClosedImmersion.restriction_range_eq_closedConnecting_ker R f n

/-- Exactness at the actual principal closed subscheme. -/
theorem boundary_range_eq_pushforward_ker (n : ℕ) :
    (boundaryG R f n).range = (pushforwardG R f n).ker :=
  Modules.Coherent.Pushforward.ClosedImmersion.closedConnecting_range_eq_pushforward_ker R f n
end AlgebraicGeometry.Scheme.PrincipalClosed
