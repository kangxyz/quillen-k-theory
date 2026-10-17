/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.CategoryTheory.FiberedCategory.CocartesianEvaluationNormalization
public import Quillen.Waldhausen.SmallModel.Whiskering

/-!
# Original coefficient composition in the common universe

The actual normalized section comparisons are lifted through the original small-model functors.
The coefficient equation is mapped through the same functor, retaining the source transport.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor
open Quillen.CategoryTheory.StrictSections Quillen.CategoryTheory.GrothendieckSections
universe u v u' v'
namespace Quillen.Waldhausen
variable {C : Type u} [Category.{v} C]
  (F : Pseudofunctor (LocallyDiscrete C) Cat.{v', u'})

/-- The original normalized comparison followed by the same universe-lifting functor. -/
def smallCoefficientIso {R S : C} (f : R ⟶ S)
    {N : F.obj ⟨R⟩ ⥤ F.obj ⟨S⟩} (n : (F.map f.toLoc).toFunctor ≅ N) :
    underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) f ⋙
        (originalEvaluation F S ⋙ AsSmall.up.{v', u', 0}) ≅
      (originalEvaluation F R ⋙ AsSmall.up.{v', u', 0}) ⋙ smallModelFunctor N :=
  (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (normalizedCoefficientIso F f n) AsSmall.up.{v', u', 0}

/-- Every lifted component is the image of the actual original normalized component. -/
theorem smallCoefficientIso_hom_app {R S : C} (f : R ⟶ S)
    {N : F.obj ⟨R⟩ ⥤ F.obj ⟨S⟩} (n : (F.map f.toLoc).toFunctor ≅ N)
    (s : underCocartesian (Pseudofunctor.Grothendieck.forget F) R) :
    (smallCoefficientIso F f n).hom.app s =
      (AsSmall.up.{v', u', 0} : F.obj ⟨S⟩ ⥤ SmallModel (F.obj ⟨S⟩)).map
        ((normalizedCoefficientIso F f n).hom.app s) := by
  simp only [smallCoefficientIso, Iso.trans_hom, Iso.symm_hom, isoWhiskerRight_hom,
    NatTrans.comp_app, Functor.associator_inv_app, whiskerRight_app, Category.id_comp]

/-- The lifted comparison is the unchanged small-model whiskering of the original coefficient. -/
theorem smallCoefficientIso_eq {R S : C} (f : R ⟶ S)
    {N : F.obj ⟨R⟩ ⥤ F.obj ⟨S⟩} (n : (F.map f.toLoc).toFunctor ≅ N) :
    smallCoefficientIso F f n =
      (Functor.associator
        (underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) f)
        (originalEvaluation F S) AsSmall.up.{v', u', 0}).symm ≪≫
        smallModelWhiskerIso (originalEvaluation F R)
          (underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) f ⋙
            originalEvaluation F S) (F.map f.toLoc).toFunctor N
          (originalCoefficientIso F f) n := rfl

/-- The genuine target composition comparison uses the original up/down cancellation. -/
def smallCoefficientCompIso {R S T : C} (f : R ⟶ S) (g : S ⟶ T)
    {Nf : F.obj ⟨R⟩ ⥤ F.obj ⟨S⟩} {Ng : F.obj ⟨S⟩ ⥤ F.obj ⟨T⟩}
    {Nfg : F.obj ⟨R⟩ ⥤ F.obj ⟨T⟩}
    (nf : (F.map f.toLoc).toFunctor ≅ Nf) (ng : (F.map g.toLoc).toFunctor ≅ Ng)
    (nfg : (F.map (f ≫ g).toLoc).toFunctor ≅ Nfg) :
    smallModelFunctor Nfg ≅ smallModelFunctor Nf ⋙ smallModelFunctor Ng :=
  isoWhiskerLeft AsSmall.down.{v', u', 0}
    (isoWhiskerRight (normalizedCoefficientCompIso F f g nf ng nfg) AsSmall.up.{v', u', 0})

/-- The full two-arrow route retains both original lifted coefficient comparisons. -/
def smallCoefficientRouteIso {R S T : C} (f : R ⟶ S) (g : S ⟶ T)
    {Nf : F.obj ⟨R⟩ ⥤ F.obj ⟨S⟩} {Ng : F.obj ⟨S⟩ ⥤ F.obj ⟨T⟩}
    (nf : (F.map f.toLoc).toFunctor ≅ Nf) (ng : (F.map g.toLoc).toFunctor ≅ Ng) :
    (underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) f ⋙
      underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) g) ⋙
        (originalEvaluation F T ⋙ AsSmall.up.{v', u', 0}) ≅
      (originalEvaluation F R ⋙ AsSmall.up.{v', u', 0}) ⋙
        smallModelFunctor Nf ⋙ smallModelFunctor Ng :=
  Functor.associator _ _ _ ≪≫
    isoWhiskerLeft _ (smallCoefficientIso F g ng) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (smallCoefficientIso F f nf) _ ≪≫ Functor.associator _ _ _

/-- Lifting preserves the proved actual coefficient composition equation. -/
theorem smallCoefficientIso_comp_hom {R S T : C} (f : R ⟶ S) (g : S ⟶ T)
    {Nf : F.obj ⟨R⟩ ⥤ F.obj ⟨S⟩} {Ng : F.obj ⟨S⟩ ⥤ F.obj ⟨T⟩}
    {Nfg : F.obj ⟨R⟩ ⥤ F.obj ⟨T⟩}
    (nf : (F.map f.toLoc).toFunctor ≅ Nf) (ng : (F.map g.toLoc).toFunctor ≅ Ng)
    (nfg : (F.map (f ≫ g).toLoc).toFunctor ≅ Nfg) :
    (smallCoefficientIso F (f ≫ g) nfg).hom ≫
        whiskerLeft (originalEvaluation F R ⋙ AsSmall.up.{v', u', 0})
          (smallCoefficientCompIso F f g nf ng nfg).hom =
      eqToHom (congrArg (fun G => G ⋙ (originalEvaluation F T ⋙ AsSmall.up.{v', u', 0}))
        (underCocartesianReindex_comp (Pseudofunctor.Grothendieck.forget F) f g)) ≫
          (smallCoefficientRouteIso F f g nf ng).hom := by
  apply NatTrans.ext
  funext s
  have h := congrArg (fun a =>
      (AsSmall.up.{v', u', 0} : F.obj ⟨T⟩ ⥤ SmallModel (F.obj ⟨T⟩)).map
      (a.app s)) (normalizedCoefficientIso_comp_hom F f g nf ng nfg)
  simpa only [smallCoefficientIso, smallCoefficientCompIso, smallCoefficientRouteIso,
    normalizedCoefficientRouteIso, Iso.trans_hom, Iso.symm_hom, isoWhiskerRight_hom,
    isoWhiskerLeft_hom, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Category.comp_id, Functor.comp_obj, smallModelFunctor, Functor.comp_map,
    Functor.map_comp, eqToHom_app, eqToHom_map, AsSmall.down_obj, AsSmall.up_obj_down,
    AsSmall.down_map, AsSmall.up_map_down] using h

/-- The actual lifted composition equation on a section object, without re-inferring categories. -/
theorem smallCoefficientIso_comp_app {R S T : C} (f : R ⟶ S) (g : S ⟶ T)
    {Nf : F.obj ⟨R⟩ ⥤ F.obj ⟨S⟩} {Ng : F.obj ⟨S⟩ ⥤ F.obj ⟨T⟩}
    {Nfg : F.obj ⟨R⟩ ⥤ F.obj ⟨T⟩}
    (nf : (F.map f.toLoc).toFunctor ≅ Nf) (ng : (F.map g.toLoc).toFunctor ≅ Ng)
    (nfg : (F.map (f ≫ g).toLoc).toFunctor ≅ Nfg)
    (s : underCocartesian (Pseudofunctor.Grothendieck.forget F) R) :
    (AsSmall.up.{v', u', 0} : F.obj ⟨T⟩ ⥤ SmallModel (F.obj ⟨T⟩)).map
        ((normalizedCoefficientIso F (f ≫ g) nfg).hom.app s) ≫
      AsSmall.up.map ((normalizedCoefficientCompIso F f g nf ng nfg).hom.app
        ((originalEvaluation F R).obj s)) =
    (eqToHom (congrArg (fun G => G ⋙ (originalEvaluation F T ⋙ AsSmall.up.{v', u', 0}))
      (underCocartesianReindex_comp (Pseudofunctor.Grothendieck.forget F) f g))).app s ≫
      AsSmall.up.map ((normalizedCoefficientIso F g ng).hom.app
        ((underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) f).obj s)) ≫
      AsSmall.up.map (Ng.map ((normalizedCoefficientIso F f nf).hom.app s)) := by
  have h := NatTrans.congr_app (smallCoefficientIso_comp_hom F f g nf ng nfg) s
  simpa only [smallCoefficientRouteIso, smallCoefficientCompIso, smallCoefficientIso_hom_app,
    Iso.trans_hom, Iso.symm_hom, isoWhiskerLeft_hom, isoWhiskerRight_hom,
    NatTrans.comp_app, whiskerLeft_app, whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.comp_id,
    smallModelFunctor, Functor.comp_obj, Functor.comp_map, eqToHom_app,
    AsSmall.down_obj, AsSmall.up_obj_down, AsSmall.down_map, AsSmall.up_map_down] using h

end Quillen.Waldhausen
