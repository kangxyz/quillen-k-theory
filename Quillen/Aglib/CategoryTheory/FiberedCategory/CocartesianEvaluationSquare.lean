/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Aglib.CategoryTheory.FiberedCategory.CocartesianEvaluationCoherence

/-!
# Original evaluation on a commuting coefficient square

For an arbitrary Cat-valued pseudofunctor, two equal composites give an evaluation square
formed from its actual composition constraints, original section transitions, and literal
section reindexing. The geometric bounded-flat evaluation square is the current consumer.
The intended upstream owner is `Aglib.CategoryTheory.FiberedCategory.CocartesianEvaluationSquare`.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Functor
open Quillen.CategoryTheory.StrictSections
universe u v u' v'
namespace Quillen.CategoryTheory.GrothendieckSections

private theorem inputSquare_of_routes {K : Type u} [Category.{v} K]
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

/-- The inverse original coefficient route retains the genuine composition constraint. -/
theorem originalCoefficientRoute_comp_hom {R S T : C} (f : R ⟶ S) (g : S ⟶ T) :
    whiskerLeft (originalEvaluation F R) (F.mapComp f.toLoc g.toLoc).hom.toNatTrans ≫
        (originalCoefficientRouteIso F f g).inv =
      (originalCoefficientIso F (f ≫ g)).inv ≫
        eqToHom (congrArg (fun G => G ⋙ originalEvaluation F T)
          (underCocartesianReindex_comp (Pseudofunctor.Grothendieck.forget F) f g)) := by
  apply (cancel_epi (originalCoefficientIso F (f ≫ g)).hom).mp
  rw [← Category.assoc, originalCoefficientIso_comp_hom]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]

/-- Equal coefficient arrows transport the inverse original coefficient comparison. -/
theorem originalCoefficientIso_congr_inv {R T : C} {f g : R ⟶ T} (h : f = g) :
    whiskerLeft (originalEvaluation F R)
        (eqToIso (congrArg (fun k : R ⟶ T => (F.map k.toLoc).toFunctor) h)).hom ≫
        (originalCoefficientIso F g).inv =
      (originalCoefficientIso F f).inv ≫
        eqToHom (congrArg (fun k : R ⟶ T =>
          underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) k ⋙
            originalEvaluation F T) h) := by
  subst g
  simp

variable {R S U T : C} (f : R ⟶ S) (g : S ⟶ T) (f' : R ⟶ U) (g' : U ⟶ T)
  (h : f ≫ g = f' ≫ g')

/-- The actual pseudofunctor composition constraints around an equal-composite square. -/
def originalCoefficientInputSquareIso :
    (F.map f.toLoc).toFunctor ⋙ (F.map g.toLoc).toFunctor ≅
      (F.map f'.toLoc).toFunctor ⋙ (F.map g'.toLoc).toFunctor :=
  (Cat.Hom.toNatIso (F.mapComp f.toLoc g.toLoc)).symm ≪≫
    eqToIso (congrArg (fun k : R ⟶ T => (F.map k.toLoc).toFunctor) h) ≪≫
    Cat.Hom.toNatIso (F.mapComp f'.toLoc g'.toLoc)

include h in
/-- The original section reindexings on an equal-composite square agree literally. -/
theorem originalReindexInputSquare :
    underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) f ⋙
        underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) g =
      underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) f' ⋙
        underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) g' :=
  (underCocartesianReindex_comp (Pseudofunctor.Grothendieck.forget F) f g).symm.trans
    ((congrArg (underCocartesianReindex (Pseudofunctor.Grothendieck.forget F)) h).trans
      (underCocartesianReindex_comp (Pseudofunctor.Grothendieck.forget F) f' g'))

/-- The complete original evaluation square on two equal coefficient composites. -/
theorem originalCoefficientInputSquare_hom :
    whiskerLeft (originalEvaluation F R) (originalCoefficientInputSquareIso F f g f' g' h).hom ≫
        (originalCoefficientRouteIso F f' g').inv =
      (originalCoefficientRouteIso F f g).inv ≫
        eqToHom (congrArg (fun G => G ⋙ originalEvaluation F T)
          (originalReindexInputSquare F f g f' g' h)) := by
  exact inputSquare_of_routes
    (isoWhiskerLeft (originalEvaluation F R) (Cat.Hom.toNatIso (F.mapComp f.toLoc g.toLoc)))
    (isoWhiskerLeft (originalEvaluation F R) (Cat.Hom.toNatIso (F.mapComp f'.toLoc g'.toLoc)))
    (whiskerLeft (originalEvaluation F R)
      (eqToIso (congrArg (fun k : R ⟶ T => (F.map k.toLoc).toFunctor) h)).hom)
    (originalCoefficientIso F (f ≫ g)).inv (originalCoefficientIso F (f' ≫ g')).inv
    (originalCoefficientRouteIso F f g).inv (originalCoefficientRouteIso F f' g').inv
    (congrArg (fun G => G ⋙ originalEvaluation F T)
      (underCocartesianReindex_comp (Pseudofunctor.Grothendieck.forget F) f g))
    (congrArg (fun G => G ⋙ originalEvaluation F T)
      (underCocartesianReindex_comp (Pseudofunctor.Grothendieck.forget F) f' g'))
    (congrArg (fun k : R ⟶ T =>
      underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) k ⋙ originalEvaluation F T) h)
    (congrArg (fun G => G ⋙ originalEvaluation F T)
      (originalReindexInputSquare F f g f' g' h))
    (originalCoefficientRoute_comp_hom F f g) (originalCoefficientRoute_comp_hom F f' g')
    (originalCoefficientIso_congr_inv F h)

end Quillen.CategoryTheory.GrothendieckSections
