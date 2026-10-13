/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.CategoryTheory.FiberedCategory.CocartesianSectionComposition
public import Quillen.CategoryTheory.FiberedCategory.GrothendieckFiberTransport

/-!
# Original coefficient comparison for cocartesian evaluation

The coefficient comparison retains the actual identity-to-arrow section transition and the
literal reindex/evaluation equality. Its coherence comes from the actual section functor laws.
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

/-- Identity evaluation after restriction is the actual coefficient fiber evaluation. -/
theorem originalFiberEvaluation_reindex {R S : C} (f : R ⟶ S) :
    underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) f ⋙
        underCocartesianEvaluation (Pseudofunctor.Grothendieck.forget F) S =
      cocartesianEvaluation (Pseudofunctor.Grothendieck.forget F)
        (Under.forget R) (Under.mk f) := by
  change cocartesianEvaluation (Pseudofunctor.Grothendieck.forget F)
      (Under.forget R) (Under.mk (f ≫ 𝟙 S)) = _
  let H : (R ⟶ S) →
      (underCocartesian (Pseudofunctor.Grothendieck.forget F) R ⥤
        Functor.Fiber (Pseudofunctor.Grothendieck.forget F) S) :=
    fun h => cocartesianEvaluation (Pseudofunctor.Grothendieck.forget F)
      (Under.forget R) (Under.mk h)
  exact congrArg H (Category.comp_id f)

/-- The actual reindexed initial arrow is the coefficient arrow after identity-object transport. -/
theorem initialArrow_reindex_transport {R S T : C} (f : R ⟶ S) (g : S ⟶ T) :
    eqToHom (congrArg Under.mk (Category.comp_id f).symm) ≫
        (Under.map f).map (initialArrow S (Under.mk g)) =
      (Under.homMk g : Under.mk f ⟶ Under.mk (f ≫ g)) := by
  apply Under.UnderMorphism.ext
  change (Under.forget R).map
    (eqToHom (congrArg Under.mk (Category.comp_id f).symm)) ≫ g = g
  rw [eqToHom_map]
  simp

/-- Original coefficient evaluation uses the actual section transition and actual base transport. -/
def originalCoefficientIso {R S : C} (f : R ⟶ S) :
    underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) f ⋙
        originalEvaluation F S ≅
      originalEvaluation F R ⋙ (F.map f.toLoc).toFunctor :=
  eqToIso (originalEvaluation_reindex F R f) ≪≫
    (originalEvaluationTransitionIso F R (Under.mk f)).symm

/-- The inverse comparison is the literal transition followed by the actual evaluation transport. -/
theorem originalCoefficientIso_inv_app {R S : C} (f : R ⟶ S)
    (s : underCocartesian (Pseudofunctor.Grothendieck.forget F) R) :
    (originalCoefficientIso F f).inv.app s =
      originalTransition F R s (Under.mk f) ≫
        (eqToIso (originalEvaluation_reindex F R f)).inv.app s := rfl

/-- The reindexed transition is the actual coefficient arrow after the original source transport. -/
theorem originalTransition_reindex_source {R S T : C} (f : R ⟶ S) (g : S ⟶ T)
    (s : underCocartesian (Pseudofunctor.Grothendieck.forget F) R) :
    (F.map g.toLoc).toFunctor.map ((eqToIso (originalEvaluation_reindex F R f)).inv.app s) ≫
        originalTransition F S
          ((underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) f).obj s)
          (Under.mk g) =
      originalArrowTransition F R s
        (Under.homMk g : Under.mk f ⟶ Under.mk (f ≫ g)) := by
  let x₀ := (cocartesianEvaluation (Pseudofunctor.Grothendieck.forget F)
    (Under.forget R) (Under.mk f)).obj s
  let x₁ := (underCocartesianEvaluation (Pseudofunctor.Grothendieck.forget F) S).obj
    ((underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) f).obj s)
  let y := (cocartesianEvaluation (Pseudofunctor.Grothendieck.forget F)
    (Under.forget R) (Under.mk (f ≫ g))).obj s
  let e : x₁ = x₀ := congrArg (fun G => G.obj s) (originalFiberEvaluation_reindex F f)
  let a := (Under.map f).map (initialArrow S (Under.mk g))
  let b : Under.mk f ⟶ Under.mk (f ≫ g) := Under.homMk g
  have ha : (Pseudofunctor.Grothendieck.forget F).IsStronglyCocartesian g
      (s.obj.val.map a) := s.property a
  have hb : (Pseudofunctor.Grothendieck.forget F).IsStronglyCocartesian g
      (s.obj.val.map b) := s.property b
  have he : eqToHom (congrArg Subtype.val e.symm) =
      s.obj.val.map (eqToHom (congrArg Under.mk (Category.comp_id f).symm)) := by
    rw [eqToHom_map]
  have hm : eqToHom (congrArg Subtype.val e.symm) ≫ s.obj.val.map a =
      s.obj.val.map b := by
    rw [he, ← s.obj.val.map_comp]
    exact congrArg s.obj.val.map (initialArrow_reindex_transport f g)
  have hn := GrothendieckFiber.liftedMap_precomp_eqToHom F g
    (x := x₀) (x' := x₁) (y := y) e.symm (s.obj.val.map a)
  have hc := GrothendieckFiber.liftedMap_congr F g (x := x₀) (y := y)
    (eqToHom (congrArg Subtype.val e.symm) ≫ s.obj.val.map a) (s.obj.val.map b) hm
  rw [← originalArrowTransition_initial F S
    ((underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) f).obj s) (Under.mk g),
    originalArrowTransition_reindex]
  simp only [eqToIso.inv, eqToHom_app]
  exact hn.symm.trans hc

/-- The original inverse coefficient comparisons retain the genuine composition constraint. -/
theorem originalCoefficientIso_comp {R S T : C} (f : R ⟶ S) (g : S ⟶ T) :
    whiskerLeft (originalEvaluation F R) (F.mapComp f.toLoc g.toLoc).hom.toNatTrans ≫
        (Functor.associator (originalEvaluation F R)
          (F.map f.toLoc).toFunctor (F.map g.toLoc).toFunctor).inv ≫
        whiskerRight (originalCoefficientIso F f).inv (F.map g.toLoc).toFunctor ≫
        (Functor.associator
          (underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) f)
          (originalEvaluation F S) (F.map g.toLoc).toFunctor).hom ≫
        whiskerLeft (underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) f)
          (originalCoefficientIso F g).inv ≫
        (Functor.associator
          (underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) f)
          (underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) g)
          (originalEvaluation F T)).inv =
      (originalCoefficientIso F (f ≫ g)).inv ≫
        eqToHom (congrArg (fun G => G ⋙ originalEvaluation F T)
          (underCocartesianReindex_comp (Pseudofunctor.Grothendieck.forget F) f g)) := by
  apply NatTrans.ext
  funext s
  simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
    Functor.associator_inv_app, Functor.associator_hom_app, Category.id_comp,
    Category.comp_id, originalCoefficientIso_inv_app, Functor.map_comp, Category.assoc]
  dsimp only [Functor.comp_obj]
  erw [Category.id_comp]
  rw [reassoc_of% originalTransition_reindex_source F f g s]
  rw [← reassoc_of% originalTransition_comp F R f g s]
  simp only [eqToIso.inv, eqToHom_app, eqToHom_trans]

/-- The actual two-coefficient route, retaining every original comparison and associator. -/
def originalCoefficientRouteIso {R S T : C} (f : R ⟶ S) (g : S ⟶ T) :
    (underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) f ⋙
      underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) g) ⋙
        originalEvaluation F T ≅
      originalEvaluation F R ⋙ (F.map f.toLoc).toFunctor ⋙ (F.map g.toLoc).toFunctor :=
  Functor.associator
      (underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) f)
      (underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) g)
      (originalEvaluation F T) ≪≫
    isoWhiskerLeft (underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) f)
      (originalCoefficientIso F g) ≪≫
    (Functor.associator
      (underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) f)
      (originalEvaluation F S) (F.map g.toLoc).toFunctor).symm ≪≫
    isoWhiskerRight (originalCoefficientIso F f) (F.map g.toLoc).toFunctor ≪≫
    Functor.associator (originalEvaluation F R)
      (F.map f.toLoc).toFunctor (F.map g.toLoc).toFunctor

/-- Forward coefficient comparisons satisfy the original two-route composition equation. -/
theorem originalCoefficientIso_comp_hom {R S T : C} (f : R ⟶ S) (g : S ⟶ T) :
    (originalCoefficientIso F (f ≫ g)).hom ≫
        whiskerLeft (originalEvaluation F R) (F.mapComp f.toLoc g.toLoc).hom.toNatTrans =
      eqToHom (congrArg (fun G => G ⋙ originalEvaluation F T)
        (underCocartesianReindex_comp (Pseudofunctor.Grothendieck.forget F) f g)) ≫
          (originalCoefficientRouteIso F f g).hom := by
  have h : whiskerLeft (originalEvaluation F R)
        (F.mapComp f.toLoc g.toLoc).hom.toNatTrans ≫
          (originalCoefficientRouteIso F f g).inv =
      (originalCoefficientIso F (f ≫ g)).inv ≫
        eqToHom (congrArg (fun G => G ⋙ originalEvaluation F T)
          (underCocartesianReindex_comp (Pseudofunctor.Grothendieck.forget F) f g)) := by
    simpa only [originalCoefficientRouteIso, Iso.trans_inv, Iso.symm_inv,
      isoWhiskerLeft_inv, isoWhiskerRight_inv, Category.assoc] using
        (originalCoefficientIso_comp F f g)
  apply (cancel_mono (originalCoefficientRouteIso F f g).inv).mp
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [h]
  simp only [Iso.hom_inv_id_assoc]

/-- At the identity coefficient, the original extracted transition is the geometric unit. -/
theorem originalTransition_id (R : C)
    (s : underCocartesian (Pseudofunctor.Grothendieck.forget F) R) :
    originalTransition F R s (Under.mk (𝟙 R)) =
      (F.mapId ⟨R⟩).hom.toNatTrans.app ((originalEvaluation F R).obj s) :=
  originalArrowTransition_id F R s (Under.mk (𝟙 R))

/-- The inverse coefficient comparison preserves the genuine pseudofunctor identity constraint. -/
theorem originalCoefficientIso_id (R : C) :
    (originalCoefficientIso F (𝟙 R)).inv ≫
        eqToHom (congrArg (fun G => G ⋙ originalEvaluation F R)
          (underCocartesianReindex_id (Pseudofunctor.Grothendieck.forget F) R)) ≫
        (Functor.leftUnitor (originalEvaluation F R)).hom =
      whiskerLeft (originalEvaluation F R) (F.mapId ⟨R⟩).hom.toNatTrans ≫
        (Functor.rightUnitor (originalEvaluation F R)).hom := by
  apply NatTrans.ext
  funext s
  simp only [NatTrans.comp_app, originalCoefficientIso_inv_app, originalTransition_id,
    eqToIso.inv, eqToHom_app, Functor.leftUnitor_hom_app, Functor.rightUnitor_hom_app,
    whiskerLeft_app, Category.assoc]
  simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

end Quillen.CategoryTheory.GrothendieckSections
