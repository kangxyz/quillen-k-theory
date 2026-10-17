/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.CategoryTheory.FiberedCategory.CocartesianEvaluationCoherence

/-!
# Original evaluation coherence after target normalization

The original coefficient comparisons are followed by specified genuine target isomorphisms.
Their two-route equation follows from the proved section equation and ordinary naturality.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Functor
open Quillen.CategoryTheory.StrictSections
universe u v u' v'
namespace Quillen.CategoryTheory.GrothendieckSections
variable {C : Type u} [Category.{v} C]
  (F : Pseudofunctor (LocallyDiscrete C) Cat.{v', u'})

/-- Follow the original coefficient comparison by the actual target normalization iso. -/
def normalizedCoefficientIso {R S : C} (f : R ⟶ S)
    {N : F.obj ⟨R⟩ ⥤ F.obj ⟨S⟩} (n : (F.map f.toLoc).toFunctor ≅ N) :
    underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) f ⋙
        originalEvaluation F S ≅ originalEvaluation F R ⋙ N :=
  originalCoefficientIso F f ≪≫ isoWhiskerLeft (originalEvaluation F R) n

/-- The original pseudofunctor constraint with the same three target normalizations. -/
def normalizedCoefficientCompIso {R S T : C} (f : R ⟶ S) (g : S ⟶ T)
    {Nf : F.obj ⟨R⟩ ⥤ F.obj ⟨S⟩} {Ng : F.obj ⟨S⟩ ⥤ F.obj ⟨T⟩}
    {Nfg : F.obj ⟨R⟩ ⥤ F.obj ⟨T⟩}
    (nf : (F.map f.toLoc).toFunctor ≅ Nf) (ng : (F.map g.toLoc).toFunctor ≅ Ng)
    (nfg : (F.map (f ≫ g).toLoc).toFunctor ≅ Nfg) : Nfg ≅ Nf ⋙ Ng :=
  nfg.symm ≪≫ Cat.Hom.toNatIso (F.mapComp f.toLoc g.toLoc) ≪≫
    isoWhiskerRight nf (F.map g.toLoc).toFunctor ≪≫ isoWhiskerLeft Nf ng

/-- The two actual normalized coefficient comparisons retain their original associators. -/
def normalizedCoefficientRouteIso {R S T : C} (f : R ⟶ S) (g : S ⟶ T)
    {Nf : F.obj ⟨R⟩ ⥤ F.obj ⟨S⟩} {Ng : F.obj ⟨S⟩ ⥤ F.obj ⟨T⟩}
    (nf : (F.map f.toLoc).toFunctor ≅ Nf) (ng : (F.map g.toLoc).toFunctor ≅ Ng) :
    (underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) f ⋙
      underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) g) ⋙
        originalEvaluation F T ≅ originalEvaluation F R ⋙ Nf ⋙ Ng :=
  Functor.associator
      (underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) f)
      (underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) g)
      (originalEvaluation F T) ≪≫
    isoWhiskerLeft (underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) f)
      (normalizedCoefficientIso F g ng) ≪≫
    (Functor.associator
      (underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) f)
      (originalEvaluation F S) Ng).symm ≪≫
    isoWhiskerRight (normalizedCoefficientIso F f nf) Ng ≪≫
    Functor.associator (originalEvaluation F R) Nf Ng

/-- Genuine target normalization preserves the proved original coefficient composition equation. -/
theorem normalizedCoefficientIso_comp_hom {R S T : C} (f : R ⟶ S) (g : S ⟶ T)
    {Nf : F.obj ⟨R⟩ ⥤ F.obj ⟨S⟩} {Ng : F.obj ⟨S⟩ ⥤ F.obj ⟨T⟩}
    {Nfg : F.obj ⟨R⟩ ⥤ F.obj ⟨T⟩}
    (nf : (F.map f.toLoc).toFunctor ≅ Nf) (ng : (F.map g.toLoc).toFunctor ≅ Ng)
    (nfg : (F.map (f ≫ g).toLoc).toFunctor ≅ Nfg) :
    (normalizedCoefficientIso F (f ≫ g) nfg).hom ≫
        whiskerLeft (originalEvaluation F R) (normalizedCoefficientCompIso F f g nf ng nfg).hom =
      eqToHom (congrArg (fun G => G ⋙ originalEvaluation F T)
        (underCocartesianReindex_comp (Pseudofunctor.Grothendieck.forget F) f g)) ≫
          (normalizedCoefficientRouteIso F f g nf ng).hom := by
  apply NatTrans.ext
  funext s
  have h := congrArg (fun a => a.app s) (originalCoefficientIso_comp_hom F f g)
  simp only [originalCoefficientRouteIso, Iso.trans_hom, Iso.symm_hom,
    isoWhiskerLeft_hom, isoWhiskerRight_hom, NatTrans.comp_app, whiskerLeft_app,
    whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id] at h
  simp only [normalizedCoefficientIso, normalizedCoefficientCompIso,
    normalizedCoefficientRouteIso, Iso.trans_hom, Iso.symm_hom, isoWhiskerLeft_hom,
    isoWhiskerRight_hom, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.map_comp,
    Category.id_comp, Category.comp_id, Category.assoc, Iso.hom_inv_id_app_assoc,
    Cat.Hom.toNatIso_hom]
  rw [reassoc_of% h]
  rw [ng.hom.naturality]
  rw [ng.hom.naturality_assoc]

end Quillen.CategoryTheory.GrothendieckSections
