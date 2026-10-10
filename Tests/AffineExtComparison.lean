/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.DerivedSingleComparison
public import Tests.AffineCechHigher

/-!
# Consumers of original affine resolution and Ext comparison

These tests retain the original Γ-resolution terms, differential and
augmentation, actual Ext maps with independent universes, and the original
`associatedDerived` morphism map. The zero ring and the zero-divisor ring
`ZMod 6` exercise negative and positive derived shifts respectively.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe w w' u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open Quillen.SchemeSheaf.AffineDerived Quillen.PerfectComplexes.Affine
open Quillen.Tests.AffineCechSections

namespace Quillen.Tests.AffineExtComparison

lemma arbitrary_injective_global_sections {R : CommRingCat.{u}}
    (I : (Spec R).Modules) [Injective I] : Injective (moduleSpecΓFunctor.obj I) :=
  inferInstance

lemma original_resolution_terms_and_differentials {R : CommRingCat.{u}}
    (M : (Spec R).Modules) [M.IsQuasicoherent]
    (I : CategoryTheory.InjectiveResolution M) (i j : ℕ) :
    (globalSectionsInjectiveResolution M I).cocomplex.X i =
      moduleSpecΓFunctor.obj (I.cocomplex.X i) ∧
    (globalSectionsInjectiveResolution M I).cocomplex.d i j =
      moduleSpecΓFunctor.map (I.cocomplex.d i j) := ⟨rfl, rfl⟩

lemma original_augmentation_degree_zero {R : CommRingCat.{u}}
    (M : (Spec R).Modules) (I : CategoryTheory.InjectiveResolution M) :
    (globalSectionsResolutionAugmentation M I).f 0 = moduleSpecΓFunctor.map (I.ι.f 0) :=
  globalSectionsResolutionAugmentation_f_zero M I

lemma original_augmentation_quasiIso {R : CommRingCat.{u}}
    (M : (Spec R).Modules) [M.IsQuasicoherent] (I : CategoryTheory.InjectiveResolution M) :
    QuasiIso (globalSectionsResolutionAugmentation M I) := inferInstance

lemma original_Ext_map_independent_universes {R : CommRingCat.{u}}
    [HasExt.{w} (ModuleCat.{u} R)] [HasExt.{w'} (Spec R).Modules]
    (X Y : ModuleCat.{u} R) (n : ℕ) :
    Function.Bijective ((tilde.functor R).mapExtAddHom X Y n :
      Ext.{w} X Y n →+ Ext.{w'} ((tilde.functor R).obj X) ((tilde.functor R).obj Y) n) :=
  tilde_mapExt_bijective X Y n

lemma projective_actual_Ext_vanishes {R : CommRingCat.{u}}
    [HasExt.{w} (Spec R).Modules] (P : ModuleCat.{u} R) [Projective P]
    (M : (Spec R).Modules) [M.IsQuasicoherent] (n : ℕ)
    (α : Ext ((tilde.functor R).obj P) M (n + 1)) : α = 0 :=
  ext_tilde_projective_eq_zero P M n α

attribute [local instance] standardDerivedModules standardDerivedSheaves

lemma original_derived_map_every_integer (R : CommRingCat.{u})
    (X Y : ModuleCat.{u} R) (n : ℤ) :
    Function.Bijective ((associatedDerived R).map :
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj X ⟶
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj Y)⟦n⟧) → _) :=
  associatedDerived_single_int_shift_map_bijective R X Y n

lemma zero_ring_original_negative_derived_map
    (X Y : ModuleCat AffineCechHigher.zeroRing) :
    Function.Bijective ((associatedDerived AffineCechHigher.zeroRing).map :
      ((DerivedCategory.singleFunctor (ModuleCat AffineCechHigher.zeroRing) 0).obj X ⟶
        ((DerivedCategory.singleFunctor (ModuleCat AffineCechHigher.zeroRing) 0).obj Y)⟦(-3 : ℤ)⟧) →
          _) :=
  associatedDerived_single_int_shift_map_bijective _ X Y (-3)

lemma torsion_ring_original_derived_morphism_lifts (X Y : ModuleCat torsionRing)
    (g : (associatedDerived torsionRing).obj
        ((DerivedCategory.singleFunctor (ModuleCat torsionRing) 0).obj X) ⟶
      (associatedDerived torsionRing).obj
        (((DerivedCategory.singleFunctor (ModuleCat torsionRing) 0).obj Y)⟦(2 : ℤ)⟧)) :
    ∃ f, (associatedDerived torsionRing).map f = g :=
  (associatedDerived_single_int_shift_map_bijective torsionRing X Y 2).surjective g

end Quillen.Tests.AffineExtComparison
