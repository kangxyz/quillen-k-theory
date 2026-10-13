/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.HomotopyGroups.PathClassBijection
public import Quillen.Topology.LocalCoefficients.RegularFunctoriality
public import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# Genuine invertibility of the regular coefficient conversion

The natural transformation is the existing map which sends each path-class
basis element to its actual image. Its component linear maps are bijective
because their basis maps are bijective. The resulting chain isomorphism has
exactly the existing coefficient chain map as its forward map.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
universe u

namespace Quillen.LocalCoefficients
variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
variable [PathConnectedSpace X]

/-- Every component of the actual regular coefficient morphism is invertible,
by linearizing the proved bijection of its original path-class basis. -/
theorem regularMap_app_isIso (f : C(X, Y)) (b : X)
    (hf : Function.Bijective (piMap 0 f (x := b) rfl)) (x : FundamentalGroupoid X) :
    IsIso ((regularMap f b).app x) := by
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  have h := pathClassMap_bijective_of_piMap f b x.as hf
  exact ⟨Finsupp.mapDomain_injective h.injective,
    Finsupp.mapDomain_surjective h.surjective⟩

/-- The existing regular conversion, rather than a substitute coefficient
map, is a natural isomorphism when the actual Pi one map is bijective. -/
theorem regularMap_isIso (f : C(X, Y)) (b : X)
    (hf : Function.Bijective (piMap 0 f (x := b) rfl)) : IsIso (regularMap f b) := by
  rw [NatTrans.isIso_iff_isIso_app]
  exact regularMap_app_isIso f b hf

/-- The supplied equality at the basepoint remains in the actual coefficient map. -/
theorem regularMapTo_isIso (f : C(X, Y)) (b : X) (b' : Y) (hb : b' = f b)
    (hf : Function.Bijective (piMap 0 f (x := b) rfl)) :
    IsIso (regularMapTo f b b' hb) := by
  subst b'
  simpa only [regularMapTo, eqToHom_refl, Category.comp_id] using regularMap_isIso f b hf

/-- The genuine regular-system isomorphism with its original forward map. -/
def regularCoefficientIso (f : C(X, Y)) (b : X) (b' : Y) (hb : b' = f b)
    (hf : Function.Bijective (piMap 0 f (x := b) rfl)) :
    regular b ≅ pullback f (regular b') := by
  let := regularMapTo_isIso f b b' hb hf
  exact asIso (regularMapTo f b b' hb)

@[simp] theorem regularCoefficientIso_hom (f : C(X, Y)) (b : X) (b' : Y)
    (hb : b' = f b) (hf : Function.Bijective (piMap 0 f (x := b) rfl)) :
    (regularCoefficientIso f b b' hb hf).hom = regularMapTo f b b' hb := rfl

/-- Applying the existing coefficient-chain functor gives an actual chain isomorphism. -/
def regularCoefficientChainIso (f : C(X, Y)) (b : X) (b' : Y) (hb : b' = f b)
    (hf : Function.Bijective (piMap 0 f (x := b) rfl)) :
    singularChainComplex (regular b) ≅ singularChainComplex (pullback f (regular b')) :=
  coefficientChainIso (regularCoefficientIso f b b' hb hf)

@[simp] theorem regularCoefficientChainIso_hom (f : C(X, Y)) (b : X) (b' : Y)
    (hb : b' = f b) (hf : Function.Bijective (piMap 0 f (x := b) rfl)) :
    (regularCoefficientChainIso f b b' hb hf).hom =
      coefficientChainMap (regularMapTo f b b' hb) := rfl

/-- The regular chain map factors through that exact isomorphism and the
original spatial pushforward, with no change to either map. -/
theorem regularPushforwardChainMap_factor (f : C(X, Y)) (b : X) (b' : Y)
    (hb : b' = f b) (hf : Function.Bijective (piMap 0 f (x := b) rfl)) :
    regularPushforwardChainMap f b b' hb =
      (regularCoefficientChainIso f b b' hb hf).hom ≫ pushforwardChainMap f (regular b') := rfl

end Quillen.LocalCoefficients
