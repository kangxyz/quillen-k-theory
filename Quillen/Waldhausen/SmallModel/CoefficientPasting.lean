/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Waldhausen.SmallModel.CoefficientCoherence

/-!
# Pasting of common-universe coefficient comparisons

The actual small-model coefficient equation retains the association of the original two routes.
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
  {R S T : C} (f : R ⟶ S) (g : S ⟶ T)
  {Nf : F.obj ⟨R⟩ ⥤ F.obj ⟨S⟩} {Ng : F.obj ⟨S⟩ ⥤ F.obj ⟨T⟩}
  {Nfg : F.obj ⟨R⟩ ⥤ F.obj ⟨T⟩}
  (nf : (F.map f.toLoc).toFunctor ≅ Nf) (ng : (F.map g.toLoc).toFunctor ≅ Ng)
  (nfg : (F.map (f ≫ g).toLoc).toFunctor ≅ Nfg)

/-- Original target normalization followed by the actual target associator. -/
def smallCoefficientTargetIso :=
  isoWhiskerLeft (originalEvaluation F R ⋙ AsSmall.up.{v', u', 0})
    (smallCoefficientCompIso F f g nf ng nfg) ≪≫
  (Functor.associator (originalEvaluation F R ⋙ AsSmall.up.{v', u', 0})
    (smallModelFunctor Nf) (smallModelFunctor Ng)).symm

/-- The actual strict source transport followed by the second coefficient comparison. -/
def smallCoefficientFirstRouteIso :=
  eqToIso (congrArg (fun G => G ⋙ (originalEvaluation F T ⋙ AsSmall.up.{v', u', 0}))
    (underCocartesianReindex_comp (Pseudofunctor.Grothendieck.forget F) f g)) ≪≫
  Functor.associator (underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) f)
    (underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) g)
    (originalEvaluation F T ⋙ AsSmall.up.{v', u', 0}) ≪≫
  isoWhiskerLeft (underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) f)
    (smallCoefficientIso F g ng) ≪≫
  (Functor.associator (underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) f)
    (originalEvaluation F S ⋙ AsSmall.up.{v', u', 0}) (smallModelFunctor Ng)).symm

/-- Original first coefficient comparison followed by normalized target pullback. -/
def smallCoefficientSecondRouteIso :=
  isoWhiskerRight (smallCoefficientIso F f nf) (smallModelFunctor Ng)

/-- The actual two-route equation, with all three original association choices retained. -/
theorem smallCoefficientPasting_hom :
    (smallCoefficientIso F (f ≫ g) nfg).hom ≫
        (smallCoefficientTargetIso F f g nf ng nfg).hom =
      (smallCoefficientFirstRouteIso F f g ng).hom ≫
        (smallCoefficientSecondRouteIso F f nf (Ng := Ng)).hom := by
  apply NatTrans.ext
  funext s
  simpa only [smallCoefficientTargetIso, smallCoefficientFirstRouteIso,
    smallCoefficientSecondRouteIso, smallCoefficientCompIso, smallCoefficientIso_hom_app,
    Iso.trans_hom, Iso.symm_hom, isoWhiskerLeft_hom, isoWhiskerRight_hom,
    NatTrans.comp_app, whiskerLeft_app, whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, eqToIso.hom, Category.id_comp, Category.comp_id,
    smallModelFunctor, Functor.comp_map, Functor.comp_obj, AsSmall.down_obj,
    AsSmall.up_obj_down, AsSmall.down_map, AsSmall.up_map_down, Category.assoc]
    using smallCoefficientIso_comp_app F f g nf ng nfg s

end Quillen.Waldhausen
