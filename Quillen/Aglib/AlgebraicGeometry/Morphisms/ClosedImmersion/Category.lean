/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.CategoryTheory.Widesubcategory
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Schemes with closed immersions

The genuine wide morphism category and its locally noetherian full subcategory retain the
original schemes and scheme maps.
-/
@[expose] public section

open AlgebraicGeometry.Scheme

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/-- Schemes with their genuine closed-immersion morphisms. -/
abbrev ClosedImmersionSchemes :=
  WideSubcategory (@IsClosedImmersion : MorphismProperty AlgebraicGeometry.Scheme.{u})

instance closedImmersionSchemes_isClosedImmersion {X Y : ClosedImmersionSchemes.{u}}
    (f : X ⟶ Y) : IsClosedImmersion f.hom := f.property

/-- Locally noetherian schemes among the genuine closed-immersion category. -/
abbrev locallyNoetherianClosedSchemeProperty : ObjectProperty ClosedImmersionSchemes.{u} :=
  fun X => IsLocallyNoetherian X.obj

/-- Locally noetherian schemes with actual closed immersions as morphisms. -/
abbrev LocallyNoetherianClosedSchemes := locallyNoetherianClosedSchemeProperty.{u}.FullSubcategory

instance locallyNoetherianClosedSchemes_isLocallyNoetherian
    (X : LocallyNoetherianClosedSchemes.{u}) : IsLocallyNoetherian X.obj.obj := X.property

end AlgebraicGeometry.Scheme
