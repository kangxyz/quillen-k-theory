/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Aglib.CategoryTheory.FiberedCategory.CocartesianEvaluationNormalization
public import Quillen.Aglib.CategoryTheory.FiberedCategory.CocartesianEvaluationSquare

/-!
# Original evaluation squares after four target normalizations

For a Cat-valued pseudofunctor, four independently specified genuine target isomorphisms
transport the original raw input square and its actual evaluation routes. The only square
hypothesis is equality of the two base composites; the normalizations need no extra
compatibility. The current consumer is the geometric normalized tensor-unit input square.
The intended upstream owner is
`Aglib.CategoryTheory.FiberedCategory.CocartesianEvaluationNormalizedSquare`.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Functor
open Quillen.CategoryTheory.StrictSections
universe u v u' v'
namespace Quillen.CategoryTheory.GrothendieckSections

private theorem normalizedInputSquare_of_routes {K : Type u} [Category.{v} K]
    {U V W X R S T O : K} (l : U ≅ V) (r : W ≅ X) (m : U ⟶ W)
    (e : U ⟶ R) (e' : W ⟶ S) (L : V ⟶ T) (R' : X ⟶ O)
    (hl : R = T) (hr : S = O) (hm : R = S) (hs : T = O)
    (hL : l.hom ≫ L = e ≫ eqToHom hl)
    (hR : r.hom ≫ R' = e' ≫ eqToHom hr)
    (hM : m ≫ e' = e ≫ eqToHom hm) :
    (l.inv ≫ m ≫ r.hom) ≫ R' = L ≫ eqToHom hs := by
  apply (cancel_epi l.hom).mp
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [hR, ← Category.assoc, hM, Category.assoc, eqToHom_trans]
  rw [← Category.assoc, hL, Category.assoc, eqToHom_trans]

variable {C : Type u} [Category.{v} C]
  (F : Pseudofunctor (LocallyDiscrete C) Cat.{v', u'})

private theorem normalizedCoefficientRoute_comp_hom {R S T : C}
    (f : R ⟶ S) (g : S ⟶ T)
    {Nf : F.obj ⟨R⟩ ⥤ F.obj ⟨S⟩} {Ng : F.obj ⟨S⟩ ⥤ F.obj ⟨T⟩}
    (nf : (F.map f.toLoc).toFunctor ≅ Nf) (ng : (F.map g.toLoc).toFunctor ≅ Ng) :
    whiskerLeft (originalEvaluation F R)
        (normalizedCoefficientCompIso F f g nf ng (Iso.refl _)).hom ≫
        (normalizedCoefficientRouteIso F f g nf ng).inv =
      (originalCoefficientIso F (f ≫ g)).inv ≫
        eqToHom (congrArg (fun G => G ⋙ originalEvaluation F T)
          (underCocartesianReindex_comp (Pseudofunctor.Grothendieck.forget F) f g)) := by
  apply (cancel_epi (normalizedCoefficientIso F (f ≫ g) (Iso.refl _)).hom).mp
  rw [← Category.assoc, normalizedCoefficientIso_comp_hom]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id,
    normalizedCoefficientIso, Iso.trans_hom, isoWhiskerLeft_hom,
    Iso.refl_hom, Functor.whiskerLeft_id', Iso.hom_inv_id_assoc]

variable {R S U T : C} (f : R ⟶ S) (g : S ⟶ T) (f' : R ⟶ U) (g' : U ⟶ T)
  (h : f ≫ g = f' ≫ g')
  {Nf : F.obj ⟨R⟩ ⥤ F.obj ⟨S⟩} {Ng : F.obj ⟨S⟩ ⥤ F.obj ⟨T⟩}
  {Nf' : F.obj ⟨R⟩ ⥤ F.obj ⟨U⟩} {Ng' : F.obj ⟨U⟩ ⥤ F.obj ⟨T⟩}
  (nf : (F.map f.toLoc).toFunctor ≅ Nf) (ng : (F.map g.toLoc).toFunctor ≅ Ng)
  (nf' : (F.map f'.toLoc).toFunctor ≅ Nf') (ng' : (F.map g'.toLoc).toFunctor ≅ Ng')

/-- The four actual target normalizations around the original raw coefficient input square. -/
def normalizedCoefficientInputSquareIso : Nf ⋙ Ng ≅ Nf' ⋙ Ng' :=
  isoWhiskerLeft Nf ng.symm ≪≫
    isoWhiskerRight nf.symm (F.map g.toLoc).toFunctor ≪≫
    originalCoefficientInputSquareIso F f g f' g' h ≪≫
    isoWhiskerRight nf' (F.map g'.toLoc).toFunctor ≪≫ isoWhiskerLeft Nf' ng'

/-- Independent target normalization preserves the original two evaluation routes. -/
theorem normalizedCoefficientInputSquare_hom :
    whiskerLeft (originalEvaluation F R)
        (normalizedCoefficientInputSquareIso F f g f' g' h nf ng nf' ng').hom ≫
        (normalizedCoefficientRouteIso F f' g' nf' ng').inv =
      (normalizedCoefficientRouteIso F f g nf ng).inv ≫
        eqToHom (congrArg (fun G => G ⋙ originalEvaluation F T)
          (originalReindexInputSquare F f g f' g' h)) := by
  have hsq := normalizedInputSquare_of_routes
    (isoWhiskerLeft (originalEvaluation F R)
      (normalizedCoefficientCompIso F f g nf ng (Iso.refl _)))
    (isoWhiskerLeft (originalEvaluation F R)
      (normalizedCoefficientCompIso F f' g' nf' ng' (Iso.refl _)))
    (whiskerLeft (originalEvaluation F R)
      (eqToIso (congrArg (fun k : R ⟶ T => (F.map k.toLoc).toFunctor) h)).hom)
    (originalCoefficientIso F (f ≫ g)).inv (originalCoefficientIso F (f' ≫ g')).inv
    (normalizedCoefficientRouteIso F f g nf ng).inv
    (normalizedCoefficientRouteIso F f' g' nf' ng').inv
    (congrArg (fun G => G ⋙ originalEvaluation F T)
      (underCocartesianReindex_comp (Pseudofunctor.Grothendieck.forget F) f g))
    (congrArg (fun G => G ⋙ originalEvaluation F T)
      (underCocartesianReindex_comp (Pseudofunctor.Grothendieck.forget F) f' g'))
    (congrArg (fun k : R ⟶ T =>
      underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) k ⋙ originalEvaluation F T) h)
    (congrArg (fun G => G ⋙ originalEvaluation F T)
      (originalReindexInputSquare F f g f' g' h))
    (normalizedCoefficientRoute_comp_hom F f g nf ng)
    (normalizedCoefficientRoute_comp_hom F f' g' nf' ng')
    (originalCoefficientIso_congr_inv F h)
  simpa only [normalizedCoefficientInputSquareIso, originalCoefficientInputSquareIso,
    normalizedCoefficientCompIso, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
    Iso.symm_inv, Iso.refl_hom, Iso.refl_inv, isoWhiskerLeft_hom, isoWhiskerLeft_inv,
    isoWhiskerRight_hom, isoWhiskerRight_inv, Functor.whiskerLeft_comp, Functor.whiskerLeft_id,
    Category.id_comp, Category.comp_id, Category.assoc] using hsq

end Quillen.CategoryTheory.GrothendieckSections
