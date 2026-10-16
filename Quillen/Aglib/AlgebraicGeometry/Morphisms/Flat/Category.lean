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
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Schemes with flat morphisms

The genuine wide morphism category and its locally noetherian full subcategory retain the original schemes and scheme maps.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/-- Schemes with genuinely flat scheme morphisms. -/

abbrev FlatSchemes := WideSubcategory (@Flat : MorphismProperty AlgebraicGeometry.Scheme.{u})

instance flatSchemes_flat {X Y : FlatSchemes.{u}} (f : X ⟶ Y) : Flat f.hom := f.property

/-- The actual locally noetherian object property on flat schemes. -/

abbrev locallyNoetherianFlatSchemeProperty : ObjectProperty FlatSchemes.{u} :=
  fun X => IsLocallyNoetherian X.obj

/-- Locally noetherian schemes with flat morphisms. -/

abbrev LocallyNoetherianFlatSchemes := locallyNoetherianFlatSchemeProperty.{u}.FullSubcategory

instance locallyNoetherianFlatSchemes_isLocallyNoetherian
    (X : LocallyNoetherianFlatSchemes.{u}) : IsLocallyNoetherian X.obj.obj := X.property

end AlgebraicGeometry.Scheme
