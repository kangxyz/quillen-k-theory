/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Pushforward
public import Aglib.AlgebraicGeometry.Modules.Coherent.Pushforward.ClosedImmersion.IdealPushforward
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.ClosedImmersion

/-!
# Principal closed schemes

The actual principal closed subscheme is the spectrum of the quotient by the principal ideal.
-/
@[expose] public section

open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

open AlgebraicGeometry.Scheme

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.PrincipalClosed

variable (R : CommRingCat.{u}) [IsNoetherianRing R] (f : R)

/-- The actual principal closed subscheme Spec(R/(f)). -/
abbrev closedScheme := Spec
  (Pushforward.ClosedImmersion.Ideal.closedRing R
    (Ideal.span {f}))

end AlgebraicGeometry.Scheme.PrincipalClosed
