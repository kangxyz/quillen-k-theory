/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.ClosedImmersion
public import Quillen.Aglib.AlgebraicGeometry.Modules.Coherent.Pushforward.ClosedImmersion.IdealSupport

/-!
# Affine closed schemes and complements

The original quotient-ring spectrum and the arbitrary open complement of V(I) are retained with
their canonical maps.
-/
@[expose] public section

open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

open AlgebraicGeometry.Scheme

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.AffineClosed

variable (R : CommRingCat.{u}) [IsNoetherianRing R] (I : Ideal R)

/-- The actual affine closed subscheme Spec(R/I). -/
abbrev closedScheme := Spec
  (Pushforward.ClosedImmersion.Ideal.closedRing R I)

/-- The actual open complement of V(I), which need not be affine. -/
abbrev openScheme :=
  (AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.ClosedImmersion.Ideal.openComplement R
  I).toScheme

/-- Its canonical open immersion into Spec R. -/
abbrev openMap :=
  AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.ClosedImmersion.Ideal.openMap R I

end AlgebraicGeometry.Scheme.AffineClosed
