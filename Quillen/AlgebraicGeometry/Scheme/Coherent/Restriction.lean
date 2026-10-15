/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.CategoryTheory.SmallModel.Exact
public import Aglib.AlgebraicGeometry.Modules.Coherent.Restriction
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Restriction
public import Quillen.AlgebraicGeometry.Scheme.Coherent.Basic
public import Aglib.AlgebraicGeometry.Modules.Support

/-!
# Exact restriction and actual support for global coherent sheaves

The affine-chart definition is stable under open restriction by composition
of actual affine charts. The full coherent inclusion reflects finite limits
and colimits, so restriction is exact. Its kernel is exactly vanishing on
the open, equivalently ordinary stalk support in the closed complement.
No global quotient-equivalence or global localization theorem is assumed.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Coherent


open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open Quillen





noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules.Coherent

variable {U X : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian U]
  (j : U ⟶ X) [IsOpenImmersion j]

/-- Its genuine canonical map on the initially upper-universe global G-groups. -/
def restrictionGMap (n : ℕ) : G X n →* G U n :=
  (coherentRestrictionExact j).smallKMap n

/-- Upper-universe G-theory with actual coherent support. -/
abbrev SupportedG (n : ℕ) : Type (u+1) :=
  CategoryTheory.ExactCategory.ExactStructure.SmallK.{u+1} (supportedCoherentExactStructure j) n

end AlgebraicGeometry.Scheme.Modules.Coherent
