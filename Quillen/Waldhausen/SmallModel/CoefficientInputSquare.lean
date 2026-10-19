/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Aglib.CategoryTheory.FiberedCategory.CocartesianEvaluationNormalizedSquare
public import Quillen.Waldhausen.SmallModel.CoefficientCoherence

/-!
# Original normalized coefficient squares in the common universe

Four genuine target normalizations transport an original coefficient input square through
the actual `AsSmall.up` and `AsSmall.down` functors. The resulting square uses the original
`smallCoefficientRouteIso` on both sides and requires only equality of the base composites.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor
open Quillen.CategoryTheory.StrictSections Quillen.CategoryTheory.GrothendieckSections
universe u v u' v'
namespace Quillen.Waldhausen

private theorem smallInputSquare_of_routes {K : Type u} [Category.{v} K]
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

private theorem smallCoefficientRoute_comp_hom {R S T : C}
    (f : R ⟶ S) (g : S ⟶ T)
    {Nf : F.obj ⟨R⟩ ⥤ F.obj ⟨S⟩} {Ng : F.obj ⟨S⟩ ⥤ F.obj ⟨T⟩}
    (nf : (F.map f.toLoc).toFunctor ≅ Nf) (ng : (F.map g.toLoc).toFunctor ≅ Ng) :
    whiskerLeft (originalEvaluation F R ⋙ AsSmall.up.{v', u', 0})
        (smallCoefficientCompIso F f g nf ng (Iso.refl _)).hom ≫
        (smallCoefficientRouteIso F f g nf ng).inv =
      (smallCoefficientIso F (f ≫ g) (Iso.refl _)).inv ≫
        eqToHom (congrArg (fun G => G ⋙ (originalEvaluation F T ⋙ AsSmall.up.{v', u', 0}))
          (underCocartesianReindex_comp (Pseudofunctor.Grothendieck.forget F) f g)) := by
  apply (cancel_epi (smallCoefficientIso F (f ≫ g) (Iso.refl _)).hom).mp
  rw [← Category.assoc, smallCoefficientIso_comp_hom]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]

private theorem smallCoefficientIso_congr_inv {R T : C} {f g : R ⟶ T} (h : f = g) :
    whiskerLeft (originalEvaluation F R ⋙ AsSmall.up.{v', u', 0})
        (isoWhiskerLeft AsSmall.down.{v', u', 0}
          (isoWhiskerRight
            (eqToIso (congrArg (fun k : R ⟶ T => (F.map k.toLoc).toFunctor) h))
            AsSmall.up.{v', u', 0})).hom ≫
        (smallCoefficientIso F g (Iso.refl _)).inv =
      (smallCoefficientIso F f (Iso.refl _)).inv ≫
        eqToHom (congrArg (fun k : R ⟶ T =>
          underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) k ⋙
            (originalEvaluation F T ⋙ AsSmall.up.{v', u', 0})) h) := by
  subst g
  simp

variable {R S U T : C} (f : R ⟶ S) (g : S ⟶ T) (f' : R ⟶ U) (g' : U ⟶ T)
  (h : f ≫ g = f' ≫ g')
  {Nf : F.obj ⟨R⟩ ⥤ F.obj ⟨S⟩} {Ng : F.obj ⟨S⟩ ⥤ F.obj ⟨T⟩}
  {Nf' : F.obj ⟨R⟩ ⥤ F.obj ⟨U⟩} {Ng' : F.obj ⟨U⟩ ⥤ F.obj ⟨T⟩}
  (nf : (F.map f.toLoc).toFunctor ≅ Nf) (ng : (F.map g.toLoc).toFunctor ≅ Ng)
  (nf' : (F.map f'.toLoc).toFunctor ≅ Nf') (ng' : (F.map g'.toLoc).toFunctor ≅ Ng')

/-- The normalized raw input square lifted with the original up/down cancellation. -/
def smallCoefficientInputSquareIso :
    smallModelFunctor Nf ⋙ smallModelFunctor Ng ≅
      smallModelFunctor Nf' ⋙ smallModelFunctor Ng' :=
  isoWhiskerLeft AsSmall.down.{v', u', 0}
    (isoWhiskerRight (normalizedCoefficientInputSquareIso F f g f' g' h nf ng nf' ng')
      AsSmall.up.{v', u', 0})

/-- The actual small-model evaluation routes preserve the independently normalized input square. -/
theorem smallCoefficientInputSquare_hom :
    whiskerLeft (originalEvaluation F R ⋙ AsSmall.up.{v', u', 0})
        (smallCoefficientInputSquareIso F f g f' g' h nf ng nf' ng').hom ≫
        (smallCoefficientRouteIso F f' g' nf' ng').inv =
      (smallCoefficientRouteIso F f g nf ng).inv ≫
        eqToHom (congrArg (fun G => G ⋙ (originalEvaluation F T ⋙ AsSmall.up.{v', u', 0}))
          (originalReindexInputSquare F f g f' g' h)) := by
  have hsq := smallInputSquare_of_routes
    (isoWhiskerLeft (originalEvaluation F R ⋙ AsSmall.up.{v', u', 0})
      (smallCoefficientCompIso F f g nf ng (Iso.refl _)))
    (isoWhiskerLeft (originalEvaluation F R ⋙ AsSmall.up.{v', u', 0})
      (smallCoefficientCompIso F f' g' nf' ng' (Iso.refl _)))
    (whiskerLeft (originalEvaluation F R ⋙ AsSmall.up.{v', u', 0})
      (isoWhiskerLeft AsSmall.down.{v', u', 0}
        (isoWhiskerRight
          (eqToIso (congrArg (fun k : R ⟶ T => (F.map k.toLoc).toFunctor) h))
          AsSmall.up.{v', u', 0})).hom)
    (smallCoefficientIso F (f ≫ g) (Iso.refl _)).inv
    (smallCoefficientIso F (f' ≫ g') (Iso.refl _)).inv
    (smallCoefficientRouteIso F f g nf ng).inv
    (smallCoefficientRouteIso F f' g' nf' ng').inv
    (congrArg (fun G => G ⋙ (originalEvaluation F T ⋙ AsSmall.up.{v', u', 0}))
      (underCocartesianReindex_comp (Pseudofunctor.Grothendieck.forget F) f g))
    (congrArg (fun G => G ⋙ (originalEvaluation F T ⋙ AsSmall.up.{v', u', 0}))
      (underCocartesianReindex_comp (Pseudofunctor.Grothendieck.forget F) f' g'))
    (congrArg (fun k : R ⟶ T =>
      underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) k ⋙
        (originalEvaluation F T ⋙ AsSmall.up.{v', u', 0})) h)
    (congrArg (fun G => G ⋙ (originalEvaluation F T ⋙ AsSmall.up.{v', u', 0}))
      (originalReindexInputSquare F f g f' g' h))
    (smallCoefficientRoute_comp_hom F f g nf ng)
    (smallCoefficientRoute_comp_hom F f' g' nf' ng')
    (smallCoefficientIso_congr_inv F h)
  simpa only [smallCoefficientInputSquareIso, normalizedCoefficientInputSquareIso,
    originalCoefficientInputSquareIso, smallCoefficientCompIso, normalizedCoefficientCompIso,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, Iso.refl_hom, Iso.refl_inv,
    isoWhiskerLeft_hom, isoWhiskerLeft_inv, isoWhiskerRight_hom, isoWhiskerRight_inv,
    whiskerLeft_comp, whiskerLeft_id, whiskerRight_comp, whiskerRight_id,
    Category.id_comp, Category.comp_id, Category.assoc] using hsq

end Quillen.Waldhausen
