/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.CategoryTheory.Widesubcategory
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Schemes with finite morphisms

The genuine wide morphism category and its locally noetherian full subcategory retain the
original schemes and scheme maps.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/-- Schemes with their genuine finite morphisms. -/
abbrev FiniteSchemes :=
  WideSubcategory (@AlgebraicGeometry.IsFinite : MorphismProperty AlgebraicGeometry.Scheme.{u})

instance finiteSchemes_isFinite {X Y : FiniteSchemes.{u}}
    (f : X ⟶ Y) : AlgebraicGeometry.IsFinite f.hom := f.property

/-- Locally noetherian schemes among the genuine finite-morphism category. -/
abbrev locallyNoetherianFiniteSchemeProperty : ObjectProperty FiniteSchemes.{u} :=
  fun X => IsLocallyNoetherian X.obj

/-- Locally noetherian schemes with actual finite morphisms as morphisms. -/
abbrev LocallyNoetherianFiniteSchemes := locallyNoetherianFiniteSchemeProperty.{u}.FullSubcategory

instance locallyNoetherianFiniteSchemes_isLocallyNoetherian
    (X : LocallyNoetherianFiniteSchemes.{u}) : IsLocallyNoetherian X.obj.obj := X.property

end AlgebraicGeometry.Scheme
