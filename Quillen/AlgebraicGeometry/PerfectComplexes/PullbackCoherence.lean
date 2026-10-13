/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Pullback

/-! Actual associativity of geometric pullback on complexes, inherited degreewise from the
original sheaf-module pullback pseudofunctor. -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes

/-- The five original geometric comparison maps compose to their literal associativity
transport. No higher coherence datum is supplied as a hypothesis. -/
lemma pullbackComplexCompIso_associativity {X Y Z T : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) :
    (pullbackComplexCompIso f (g ≫ h)).hom ≫
      Functor.whiskerRight (pullbackComplexCompIso g h).hom (pullbackComplex f) ≫
      (Functor.associator (pullbackComplex h) (pullbackComplex g) (pullbackComplex f)).hom ≫
      Functor.whiskerLeft (pullbackComplex h) (pullbackComplexCompIso f g).inv ≫
      (pullbackComplexCompIso (f ≫ g) h).inv = eqToHom (by simp) := by
  apply NatTrans.ext
  funext K
  apply HomologicalComplex.hom_ext
  intro n
  simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    HomologicalComplex.comp_f, eqToHom_app, HomologicalComplex.eqToHom_f,
    pullbackComplexCompIso, pullbackComplex, Iso.symm_hom, Iso.symm_inv,
    Functor.mapHomologicalComplexCompIso_hom_app_f,
    Functor.mapHomologicalComplexCompIso_inv_app_f, Functor.mapHomologicalComplex_map_f,
    Functor.associator_hom_app, HomologicalComplex.id_f, Functor.comp_obj,
    Functor.mapHomologicalComplex_obj_X, Category.id_comp] using
    congrArg (fun η ↦ η.app (K.X n)) (Scheme.Modules.pseudofunctor_associativity f g h)

/-- The two original decompositions of a triple pullback agree, including the genuine functor
associator and the original scheme-composition transport. -/
lemma pullbackComplexCompIso_two_routes {X Y Z T : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) :
    (pullbackComplexCompIso f (g ≫ h)).hom ≫
      Functor.whiskerRight (pullbackComplexCompIso g h).hom (pullbackComplex f) ≫
      (Functor.associator (pullbackComplex h) (pullbackComplex g) (pullbackComplex f)).hom =
    eqToHom (by simp) ≫ (pullbackComplexCompIso (f ≫ g) h).hom ≫
      Functor.whiskerLeft (pullbackComplex h) (pullbackComplexCompIso f g).hom := by
  let e := Functor.isoWhiskerLeft (pullbackComplex h) (pullbackComplexCompIso f g)
  apply (cancel_mono (e.inv ≫ (pullbackComplexCompIso (f ≫ g) h).inv)).mp
  change _ = (eqToHom (by simp) ≫ (pullbackComplexCompIso (f ≫ g) h).hom ≫ e.hom) ≫
    (e.inv ≫ (pullbackComplexCompIso (f ≫ g) h).inv)
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]
  simpa only [e, Functor.isoWhiskerLeft_inv] using pullbackComplexCompIso_associativity f g h

end Quillen.PerfectComplexes
