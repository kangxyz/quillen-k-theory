/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Pullback
public import Aglib.AlgebraicGeometry.Modules.Coherent.FlatPullback
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FlatPullback
public import Mathlib.CategoryTheory.Widesubcategory
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Pullback
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Coherent

/-!
# Pullback and the coherent inclusion

The actual vector-bundle inclusion commutes with arbitrary sheaf pullback before flatness is needed
for exactness.-/
@[expose] public section

open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme

variable {X Y Z : AlgebraicGeometry.Scheme.{u}}
  [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian Z]

omit [IsLocallyNoetherian X] in
/-- The actual bundle-to-coherent inclusion commutes with arbitrary pullback
as a functor, before flatness is needed for the coherent exact structure. -/
theorem vectorBundleToCoherent_pullback (f : X ⟶ Y) :
    AlgebraicGeometry.Scheme.Modules.vectorBundleToCoherent Y ⋙
      AlgebraicGeometry.Scheme.Modules.QuasiCoherent.finiteTypePullback f =
      AlgebraicGeometry.Scheme.Modules.vectorBundlePullback f ⋙
        AlgebraicGeometry.Scheme.Modules.vectorBundleToCoherent X := rfl

end AlgebraicGeometry.Scheme
