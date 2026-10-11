/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.PullbackCoherence
public import Quillen.AlgebraicGeometry.PerfectComplexes.PullbackUnitCoherence

/-! Actual bounded-flat pullback identity coherence, reflected through the faithful inclusion. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes

/-- The genuine left unit comparison on the original bounded-flat categories. -/
lemma boundedFlatPerfectPullbackCompIso_left_unitality {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (boundedFlatPerfectPullbackCompIso f (𝟙 Y)).hom ≫
      Functor.whiskerRight (boundedFlatPerfectPullbackIdIso Y).hom
        (boundedFlatPerfectPullback f) ≫
      (Functor.leftUnitor _).hom = eqToHom (by simp) := by
  apply NatTrans.ext
  funext K
  apply (boundedFlatPerfect X).ι.map_injective
  simp only [NatTrans.comp_app, Functor.map_comp, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    boundedFlatPerfectPullbackCompIso, boundedFlatPerfectPullbackIdIso,
    Functor.fullyFaithfulCancelRight_hom_app, Functor.map_preimage,
    Functor.isoWhiskerLeft_hom, eqToHom_app, eqToHom_map, Functor.leftUnitor_hom_app,
    boundedFlatPerfectPullback, ObjectProperty.ι_obj_lift_map, Functor.comp_obj,
    Functor.comp_map, ObjectProperty.ι_obj, ObjectProperty.lift_obj_obj]
  simpa using
    congrArg (fun η => η.app K.obj) (pullbackComplexCompIso_left_unitality f)

/-- The genuine right unit comparison on the original bounded-flat categories. -/
lemma boundedFlatPerfectPullbackCompIso_right_unitality {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (boundedFlatPerfectPullbackCompIso (𝟙 X) f).hom ≫
      Functor.whiskerLeft (boundedFlatPerfectPullback f)
        (boundedFlatPerfectPullbackIdIso X).hom ≫
      (Functor.rightUnitor _).hom = eqToHom (by simp) := by
  apply NatTrans.ext
  funext K
  apply (boundedFlatPerfect X).ι.map_injective
  simp only [NatTrans.comp_app, Functor.map_comp, Functor.whiskerLeft_app,
    boundedFlatPerfectPullbackCompIso, boundedFlatPerfectPullbackIdIso,
    Functor.fullyFaithfulCancelRight_hom_app, Functor.map_preimage,
    Functor.isoWhiskerLeft_hom, eqToHom_app, eqToHom_map, Functor.rightUnitor_hom_app,
    boundedFlatPerfectPullback, Functor.comp_obj, ObjectProperty.ι_obj,
    ObjectProperty.lift_obj_obj]
  simpa using
    congrArg (fun η => η.app K.obj) (pullbackComplexCompIso_right_unitality f)

end Quillen.PerfectComplexes
