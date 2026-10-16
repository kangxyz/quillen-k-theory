/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.CategoryTheory.Widesubcategory
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.RingTheory.Noetherian.Defs

/-!
# Commutative rings with finite homomorphisms

Finite coordinate homomorphisms form a multiplicative wide subcategory,
with a full noetherian subcategory.
-/
@[expose] public section

noncomputable section
universe u v w
open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/-- The genuine finite coordinate-ring homomorphisms. -/
def finiteRingHom : MorphismProperty CommRingCat.{u} := fun _ _ φ => φ.hom.Finite

instance finiteRingHom_multiplicative : finiteRingHom.{u}.IsMultiplicative where
  id_mem R := RingHom.Finite.id R
  comp_mem _ _ hf hg := hg.comp hf

/-- Commutative rings with actual finite ring homomorphisms as morphisms. -/
abbrev FiniteRings := WideSubcategory finiteRingHom.{u}

/-- The noetherian coordinate-ring property in the category of finite ring maps. -/
abbrev noetherianFiniteRingProperty : ObjectProperty FiniteRings.{u} :=
  fun R => IsNoetherianRing R.obj

/-- Noetherian coordinate rings with actual finite morphisms. -/
abbrev NoetherianFiniteRings := noetherianFiniteRingProperty.{u}.FullSubcategory

instance noetherianFiniteRings_noetherian (R : NoetherianFiniteRings.{u}) :
    IsNoetherianRing R.obj.obj := R.property

end AlgebraicGeometry.Scheme
