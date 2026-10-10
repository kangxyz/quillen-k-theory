/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
import Quillen.Scheme.Sheaf.AffineExtComparison
import Quillen.PerfectComplexes.Affine.DerivedComparison

/-!
# Actual affine derived morphisms between shifted single objects

The original `associatedDerived` comparison induces a bijection on morphisms
from a module in degree zero to any integer shift of another module in
degree zero. Positive degrees use bijectivity of the original tilde Ext map,
identified with the actual derived map using its existing single-object and
shift isomorphisms. Negative degrees use the canonical derived t-structure.

This is actual derived-morphism bijectivity on shifted single objects.
Full faithfulness on bounded complexes and the quasicoherent-cohomology
essential image remain separate comparison theorems.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
namespace Quillen.PerfectComplexes.Affine

attribute [local instance] standardDerivedModules standardDerivedSheaves

lemma associatedDerived_single_shift_map_bijective (R : CommRingCat.{u})
    (X Y : ModuleCat.{u} R) (n : ℕ) :
    Function.Bijective ((associatedDerived R).map :
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj X ⟶
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj Y)⟦(n : ℤ)⟧) → _) := by
  let : HasExt.{u + 1} (ModuleCat.{u} R) := hasExt_of_hasDerivedCategory _
  let : HasExt.{u + 1} (Spec R).Modules := hasExt_of_hasDerivedCategory _
  let F := tilde.functor R
  let eX := (F.mapDerivedCategorySingleFunctor 0).app X
  let eY := (F.mapDerivedCategorySingleFunctor 0).app Y
  let eB := (F.mapDerivedCategory.commShiftIso (n : ℤ)).app
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj Y) ≪≫
    (shiftFunctor _ (n : ℤ)).mapIso eY
  let e := Iso.homCongr eX eB
  have h (α : Ext.{u + 1} X Y n) :
      e ((associatedDerived R).map α.hom) = (α.mapExactFunctor F).hom := by
    rw [Ext.mapExactFunctor_hom]
    simp only [e, eX, eB, eY, Iso.homCongr_apply, Iso.trans_hom, Functor.mapIso_hom,
      ShiftedHom.map, Category.assoc]
    rfl
  have hbij := SchemeSheaf.AffineDerived.tilde_mapExt_bijective X Y n
  constructor
  · intro f g hfg
    obtain ⟨α, rfl⟩ := (Ext.homEquiv (X := X) (Y := Y) (n := n)).surjective f
    obtain ⟨β, rfl⟩ := (Ext.homEquiv (X := X) (Y := Y) (n := n)).surjective g
    apply congrArg Ext.hom
    apply hbij.injective
    apply Ext.homEquiv.injective
    change (α.mapExactFunctor F).hom = (β.mapExactFunctor F).hom
    rw [← h, ← h, hfg]
  · intro f
    obtain ⟨β, hβ⟩ := (Ext.homEquiv (X := F.obj X) (Y := F.obj Y) (n := n)).surjective (e f)
    obtain ⟨α, hα⟩ := hbij.surjective β
    refine ⟨α.hom, e.injective ?_⟩
    rw [h]
    exact (congrArg Ext.hom hα).trans hβ

lemma _root_.DerivedCategory.single_negative_shift_hom_subsingleton {C : Type*} [Category* C] [Abelian C]
    [HasDerivedCategory C] (X Y : C) (n : ℤ) (hn : n < 0) :
    Subsingleton ((DerivedCategory.singleFunctor C 0).obj X ⟶
      ((DerivedCategory.singleFunctor C 0).obj Y)⟦n⟧) := by
  let t := DerivedCategory.TStructure.t (C := C)
  let : t.IsGE (((DerivedCategory.singleFunctor C 0).obj Y)⟦n⟧) (-n) :=
    t.isGE_shift _ 0 n (-n) (by omega)
  exact ⟨fun f g => (t.zero f 0 (-n) (by omega)).trans (t.zero g 0 (-n) (by omega)).symm⟩

/-- Actual affine derived morphisms between single objects agree in every
integer degree. The functor here is the original `associatedDerived`. -/
lemma associatedDerived_single_int_shift_map_bijective (R : CommRingCat.{u})
    (X Y : ModuleCat.{u} R) (n : ℤ) :
    Function.Bijective ((associatedDerived R).map :
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj X ⟶
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj Y)⟦n⟧) → _) := by
  obtain hn | hn := le_or_gt 0 n
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    exact associatedDerived_single_shift_map_bijective R X Y m
  · let F := tilde.functor R
    let eX := (F.mapDerivedCategorySingleFunctor 0).app X
    let eY := (F.mapDerivedCategorySingleFunctor 0).app Y
    let eB := (F.mapDerivedCategory.commShiftIso n).app
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj Y) ≪≫
      (shiftFunctor _ n).mapIso eY
    let e := Iso.homCongr eX eB
    have hsrc := DerivedCategory.single_negative_shift_hom_subsingleton X Y n hn
    have htgt := DerivedCategory.single_negative_shift_hom_subsingleton (F.obj X) (F.obj Y) n hn
    refine ⟨fun f g _ => hsrc.elim f g, fun f => ⟨0, ?_⟩⟩
    apply e.injective
    exact htgt.elim _ _

end Quillen.PerfectComplexes.Affine
