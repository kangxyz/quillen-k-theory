/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.ClosedImmersion.Noetherian
public import Quillen.Aglib.AlgebraicGeometry.Modules.Coherent.Pushforward.ClosedImmersion.Support

/-!
# Closed sources and their open complements

A closed subscheme of a noetherian scheme is noetherian. The actual complement and its
canonical open immersion retain the original closed-image geometry.
-/
@[expose] public section

open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

open AlgebraicGeometry.Scheme

noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Closed

variable {Z X : AlgebraicGeometry.Scheme.{u}} [IsNoetherian X]
  (i : Z ⟶ X) [IsClosedImmersion i]

include i in
/-- A closed subscheme of a noetherian scheme is locally noetherian. -/
theorem source_locallyNoetherian : IsLocallyNoetherian Z :=
  AlgebraicGeometry.Scheme.closedSource_isLocallyNoetherian i

include i in
/-- The stronger global noetherianity conclusion is also derived. -/
theorem source_noetherian : IsNoetherian Z :=
  AlgebraicGeometry.Scheme.closedSource_isNoetherian i

/-- The actual open complement of the closed image. -/
abbrev openScheme :=
  (AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.ClosedImmersion.openComplement i).toScheme

/-- Its actual geometric open immersion. -/
abbrev openMap := AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.ClosedImmersion.openMap i

end AlgebraicGeometry.Scheme.Closed
