/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.Scheme.Coherent.Finite.AffineFunctoriality
public import Mathlib.CategoryTheory.Widesubcategory

/-! # The original public G-groups form a genuine covariant pushforward functor on affine schemes
  represented by noetherian rings and finite coordinate maps. General proper direct image is a
  further construction. -/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory AlgebraicGeometry
namespace Quillen.Scheme

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

/-- Actual finite affine G-pushforward, covariant on the represented affine schemes. -/
def GFiniteAffinePushforwardFunctor (n : ℕ) : NoetherianFiniteRings.{u}ᵒᵖ ⥤ GrpCat.{u+1} where
  obj R := GrpCat.of (CoherentScheme.G (Spec R.unop.obj.obj) n)
  map f := GrpCat.ofHom
    (CoherentScheme.FiniteAffine.pushforwardG f.unop.hom.hom f.unop.hom.property n)
  map_id R := by
    apply GrpCat.hom_ext
    exact CoherentScheme.FiniteAffine.pushforwardG_id R.unop.obj.obj n
  map_comp f g := by
    apply GrpCat.hom_ext
    exact CoherentScheme.FiniteAffine.pushforwardG_comp
      g.unop.hom.hom g.unop.hom.property f.unop.hom.hom f.unop.hom.property n

@[simp] theorem GFiniteAffinePushforwardFunctor_map {R S : NoetherianFiniteRings.{u}}
    (φ : R ⟶ S) (n : ℕ) :
    ((GFiniteAffinePushforwardFunctor n).map φ.op).hom =
      CoherentScheme.FiniteAffine.pushforwardG φ.hom.hom φ.hom.property n := rfl

end Quillen.Scheme
