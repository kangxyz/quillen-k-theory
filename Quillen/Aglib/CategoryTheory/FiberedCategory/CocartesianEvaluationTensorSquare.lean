/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Aglib.CategoryTheory.FiberedCategory.CocartesianEvaluationSquare

/-!
# Original evaluation squares with specified input comparisons

An arbitrary Cat-valued pseudofunctor and two equal coefficient composites retain their
original evaluation square when the first and last input functors are replaced through
specified natural isomorphisms. Both input comparisons remain in the resulting square.
The current consumer uses the actual geometric tensor-unit functors and their genuine unitors;
no monoidal structure or tensor comparison is reconstructed here.
The intended upstream owner is
`Aglib.CategoryTheory.FiberedCategory.CocartesianEvaluationTensorSquare`.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Functor
open Quillen.CategoryTheory.StrictSections
universe u v u' v'
namespace Quillen.CategoryTheory.GrothendieckSections

private theorem extendInputSquare {K : Type u} [Category.{v} K]
    {A B C D E F U V : K} (u : A ≅ B) (v : C ≅ D)
    (l : B ⟶ U) (m : U ⟶ V) (r : V ⟶ D)
    (L : B ⟶ E) (R : D ⟶ F) (k : E ⟶ F) (h : (l ≫ m ≫ r) ≫ R = L ≫ k) :
    (u.hom ≫ l ≫ m ≫ r ≫ v.inv) ≫ (v.hom ≫ R) = (u.hom ≫ L) ≫ k := by
  simpa only [Category.assoc, Iso.inv_hom_id_assoc] using congrArg (u.hom ≫ ·) h

variable {C : Type u} [Category.{v} C]
  (F : Pseudofunctor (LocallyDiscrete C) Cat.{v', u'})
  {R S U T : C} (f : R ⟶ S) (g : S ⟶ T) (f' : R ⟶ U) (g' : U ⟶ T)
  (h : f ≫ g = f' ≫ g')
  (P : F.obj ⟨R⟩ ⥤ F.obj ⟨S⟩) (Q : F.obj ⟨U⟩ ⥤ F.obj ⟨T⟩)
  (eP : P ≅ (F.map f.toLoc).toFunctor) (eQ : Q ≅ (F.map g'.toLoc).toFunctor)

/-- The original raw input square with its two specified input comparisons. -/
def originalCoefficientTensorInputIso :
    P ⋙ (F.map g.toLoc).toFunctor ≅ (F.map f'.toLoc).toFunctor ⋙ Q :=
  isoWhiskerRight eP (F.map g.toLoc).toFunctor ≪≫
    (Cat.Hom.toNatIso (F.mapComp f.toLoc g.toLoc)).symm ≪≫
    eqToIso (congrArg (fun k : R ⟶ T => (F.map k.toLoc).toFunctor) h) ≪≫
    Cat.Hom.toNatIso (F.mapComp f'.toLoc g'.toLoc) ≪≫
    isoWhiskerLeft (F.map f'.toLoc).toFunctor eQ.symm

/-- The first input comparison precedes the unchanged original evaluation route. -/
def originalCoefficientTensorEvaluationLeft :
    originalEvaluation F R ⋙ (P ⋙ (F.map g.toLoc).toFunctor) ≅
      (underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) f ⋙
        underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) g) ⋙
        originalEvaluation F T :=
  isoWhiskerLeft (originalEvaluation F R) (isoWhiskerRight eP (F.map g.toLoc).toFunctor) ≪≫
    (originalCoefficientRouteIso F f g).symm

/-- The second input comparison precedes the unchanged original evaluation route. -/
def originalCoefficientTensorEvaluationRight :
    originalEvaluation F R ⋙ ((F.map f'.toLoc).toFunctor ⋙ Q) ≅
      (underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) f' ⋙
        underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) g') ⋙
        originalEvaluation F T :=
  isoWhiskerLeft (originalEvaluation F R) (isoWhiskerLeft (F.map f'.toLoc).toFunctor eQ) ≪≫
    (originalCoefficientRouteIso F f' g').symm

/-- The original evaluated input square keeps both actual chosen comparison isomorphisms. -/
theorem originalCoefficientTensorInputSquare_hom :
    whiskerLeft (originalEvaluation F R)
        (originalCoefficientTensorInputIso F f g f' g' h P Q eP eQ).hom ≫
        (originalCoefficientTensorEvaluationRight F f' g' Q eQ).hom =
      (originalCoefficientTensorEvaluationLeft F f g P eP).hom ≫
        eqToHom (congrArg (fun G => G ⋙ originalEvaluation F T)
          (originalReindexInputSquare F f g f' g' h)) := by
  exact extendInputSquare
    (isoWhiskerLeft (originalEvaluation F R) (isoWhiskerRight eP (F.map g.toLoc).toFunctor))
    (isoWhiskerLeft (originalEvaluation F R) (isoWhiskerLeft (F.map f'.toLoc).toFunctor eQ))
    (whiskerLeft (originalEvaluation F R) (F.mapComp f.toLoc g.toLoc).inv.toNatTrans)
    (whiskerLeft (originalEvaluation F R)
      (eqToIso (congrArg (fun k : R ⟶ T => (F.map k.toLoc).toFunctor) h)).hom)
    (whiskerLeft (originalEvaluation F R) (F.mapComp f'.toLoc g'.toLoc).hom.toNatTrans)
    (originalCoefficientRouteIso F f g).inv (originalCoefficientRouteIso F f' g').inv
    (eqToHom (congrArg (fun G => G ⋙ originalEvaluation F T)
      (originalReindexInputSquare F f g f' g' h)))
    (originalCoefficientInputSquare_hom F f g f' g' h)

end Quillen.CategoryTheory.GrothendieckSections
