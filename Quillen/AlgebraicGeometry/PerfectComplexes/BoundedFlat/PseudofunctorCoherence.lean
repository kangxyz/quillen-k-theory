/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.Pseudofunctor

/-!
# Original geometric components of the affine pseudofunctor

The affine composition constraint retains the original `Spec` composition equality and the
original bounded-flat pullback comparison. No replacement comparison is introduced.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Bicategory AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes

/-- The affine constraint is the original geometric comparison after actual `Spec` transport. -/
theorem boundedFlatAffinePseudofunctor_mapComp_hom {R S T : CommRingCat.{u}}
    (f : R ⟶ S) (g : S ⟶ T) :
    (boundedFlatAffinePseudofunctor.mapComp f.toLoc g.toLoc).hom.toNatTrans =
      eqToHom (congrArg boundedFlatPerfectPullback (Spec.map_comp f g)) ≫
        (boundedFlatPerfectPullbackCompIso (Spec.map g) (Spec.map f)).hom := by
  simp only [boundedFlatAffinePseudofunctor, Pseudofunctor.comp_mapComp,
    Iso.trans_hom, Cat.Hom.toNatTrans_comp, PrelaxFunctor.map₂Iso_hom,
    Functor.toPseudofunctor_mapComp]
  dsimp only [Quiver.Hom.toLoc]
  simp only [eqToIso.hom, PrelaxFunctor.map₂_eqToHom, Cat.Hom₂.eqToHom_toNatTrans]
  rfl

/-- The affine unit is the original geometric identity comparison after actual `Spec` transport. -/
theorem boundedFlatAffinePseudofunctor_mapId_hom (R : CommRingCat.{u}) :
    (boundedFlatAffinePseudofunctor.mapId ⟨R⟩).hom.toNatTrans =
      eqToHom (congrArg boundedFlatPerfectPullback (Spec.map_id R)) ≫
        (boundedFlatPerfectPullbackIdIso (Spec R)).hom := by
  simp only [boundedFlatAffinePseudofunctor, Pseudofunctor.comp_mapId,
    Iso.trans_hom, Cat.Hom.toNatTrans_comp, PrelaxFunctor.map₂Iso_hom,
    Functor.toPseudofunctor_mapId, eqToIso.hom, PrelaxFunctor.map₂_eqToHom,
    Cat.Hom₂.eqToHom_toNatTrans]
  rfl

end Quillen.PerfectComplexes
