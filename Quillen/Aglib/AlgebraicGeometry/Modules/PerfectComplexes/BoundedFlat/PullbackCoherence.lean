/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.PullbackIsomorphisms
public import Quillen.Aglib.AlgebraicGeometry.Modules.Complex.PullbackCoherence

/-! Actual pullback associativity on bounded-flat perfect complexes for arbitrary scheme maps. -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes

/-- The original bounded-flat pullback comparisons satisfy the actual geometric associativity
loop, inherited through the faithful inclusion into complexes. -/
lemma boundedFlatPerfectPullbackCompIso_associativity {X Y Z T : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) :
    (boundedFlatPerfectPullbackCompIso f (g ≫ h)).hom ≫
      Functor.whiskerRight (boundedFlatPerfectPullbackCompIso g h).hom
        (boundedFlatPerfectPullback f) ≫
      (Functor.associator (boundedFlatPerfectPullback h) (boundedFlatPerfectPullback g)
        (boundedFlatPerfectPullback f)).hom ≫
      Functor.whiskerLeft (boundedFlatPerfectPullback h)
        (boundedFlatPerfectPullbackCompIso f g).inv ≫
      (boundedFlatPerfectPullbackCompIso (f ≫ g) h).inv = eqToHom (by simp) := by
  apply NatTrans.ext
  funext K
  simp only [NatTrans.comp_app, Functor.associator_hom_app, Category.id_comp]
  apply (boundedFlatPerfect X).ι.map_injective
  simpa only [NatTrans.comp_app, Functor.map_comp, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, boundedFlatPerfectPullbackCompIso,
    Functor.fullyFaithfulCancelRight_hom_app, Functor.fullyFaithfulCancelRight_inv_app,
    Functor.map_preimage, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
    eqToHom_app, eqToHom_map, Functor.associator_hom_app, Functor.map_id,
    boundedFlatPerfectPullback, ObjectProperty.ι_obj_lift_obj,
    ObjectProperty.ι_obj_lift_map, Functor.comp_obj, Functor.comp_map,
    ObjectProperty.ι_obj, ObjectProperty.lift_obj_obj, Category.id_comp] using
    congrArg (fun η ↦ η.app K.obj) (pullbackComplexCompIso_associativity f g h)

/-- The two original decompositions of a triple pullback agree, including the genuine functor
associator and the original scheme-composition transport. -/
lemma boundedFlatPerfectPullbackCompIso_two_routes {X Y Z T : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) :
    (boundedFlatPerfectPullbackCompIso f (g ≫ h)).hom ≫
      Functor.whiskerRight (boundedFlatPerfectPullbackCompIso g h).hom
        (boundedFlatPerfectPullback f) ≫
      (Functor.associator (boundedFlatPerfectPullback h) (boundedFlatPerfectPullback g)
        (boundedFlatPerfectPullback f)).hom =
    eqToHom (by simp) ≫ (boundedFlatPerfectPullbackCompIso (f ≫ g) h).hom ≫
      Functor.whiskerLeft (boundedFlatPerfectPullback h)
        (boundedFlatPerfectPullbackCompIso f g).hom := by
  let e := Functor.isoWhiskerLeft (boundedFlatPerfectPullback h)
    (boundedFlatPerfectPullbackCompIso f g)
  apply (cancel_mono (e.inv ≫ (boundedFlatPerfectPullbackCompIso (f ≫ g) h).inv)).mp
  change _ = (eqToHom (by simp) ≫ (boundedFlatPerfectPullbackCompIso (f ≫ g) h).hom ≫ e.hom) ≫
    (e.inv ≫ (boundedFlatPerfectPullbackCompIso (f ≫ g) h).inv)
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]
  simpa only [e, Functor.isoWhiskerLeft_inv] using
    boundedFlatPerfectPullbackCompIso_associativity f g h


end Quillen.PerfectComplexes
