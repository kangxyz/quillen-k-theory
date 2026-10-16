/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.CategoryTheory.Widesubcategory
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Schemes with open immersions

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

/-- Schemes with only open immersions as morphisms. -/
abbrev OpenImmersionSchemes :=
  WideSubcategory (@IsOpenImmersion : MorphismProperty AlgebraicGeometry.Scheme.{u})

instance openImmersionSchemes_isOpenImmersion {X Y : OpenImmersionSchemes.{u}}
    (f : X ⟶ Y) : IsOpenImmersion f.hom := f.property

/-- Local noetherianity as an object property of the open-immersion category. -/
abbrev locallyNoetherianOpenSchemeProperty : ObjectProperty OpenImmersionSchemes.{u} :=
  fun X => IsLocallyNoetherian X.obj

/-- Locally noetherian schemes with only open immersions as morphisms. -/
abbrev LocallyNoetherianOpenSchemes :=
  locallyNoetherianOpenSchemeProperty.{u}.FullSubcategory

instance locallyNoetherianOpenSchemes_isLocallyNoetherian
    (X : LocallyNoetherianOpenSchemes.{u}) : IsLocallyNoetherian X.obj.obj := X.property

/-- The inclusion retains the open-immersion restriction on morphisms. -/
abbrev locallyNoetherianOpenSchemesInclusion :
    LocallyNoetherianOpenSchemes.{u} ⥤ OpenImmersionSchemes.{u} :=
  locallyNoetherianOpenSchemeProperty.{u}.ι

end AlgebraicGeometry.Scheme
