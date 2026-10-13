/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSectionEvaluationSourceLeg
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CompositionTrack
public import Quillen.Waldhausen.SmallModel.CoefficientPasting
public import Quillen.Waldhausen.SConstruction.Iterated.PrespectrumPastingHomotopy
public import Quillen.Waldhausen.SConstruction.Iterated.PrespectrumTransformationTransport
public import Quillen.Topology.Prespectrum.RelativeHomotopyLevels
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TripleTrack
public import Quillen.Waldhausen.SConstruction.Iterated.PrespectrumHomotopyNaturality
public import Quillen.Topology.Prespectrum.RelativeHomotopyHorizontal
public import Quillen.Topology.Prespectrum.RelativeHomotopyWhiskering
public import Quillen.Topology.Prespectrum.RelativeHomotopyStrictSquarePasting
public import Quillen.Topology.Prespectrum.HomotopySquareOfPasting
public import Quillen.Topology.Prespectrum.PushoutMovingHomotopy

/-!
# Native evaluation composition and original Laurent chart descent

The existing native evaluation isomorphisms satisfy the joint composition equation with
both original zero normalizations and the common-universe lift retained. The component
condition is proved before specialization and exported as the equality of the original
natural-transformation pastings in `boundedFlatCoefficientSectionModelPasting_hom`.

Its relative prespectrum comparison uses the original split geometric composition track.
Specialization to the actual positive and inverse native Laurent charts gives the moving
comparison-map homotopy on the original fine and raw pushouts. Its two chart faces and
cylinder formula retain the independent comparison, cylinder and structure parameters.

Cone/source-null, seed and telescope evaluation comparisons are subsequent obligations.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open Quillen.Scheme.CoefficientBaseChange
universe u
namespace Quillen.PerfectComplexes

private def rebaseComparison
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (S : A ⥤ B) (P : C ⥤ D) {U₀ E₀ : A ⥤ C} {U₁ E₁ : B ⥤ D}
    (κ : S ⋙ U₁ ≅ U₀ ⋙ P) (z₀ : U₀ ≅ E₀) (z₁ : U₁ ≅ E₁) :=
  isoWhiskerLeft S z₁.symm ≪≫ κ ≪≫ isoWhiskerRight z₀ P

private theorem rebaseComparison_pasting
    {A B C D E F : Type*} [Category A] [Category B] [Category C]
    [Category D] [Category E] [Category F]
    (Sf : A ⥤ B) (Sg : B ⥤ C) (Sfg : A ⥤ C) (hS : Sfg = Sf ⋙ Sg)
    (Pf : D ⥤ E) (Pg : E ⥤ F) (Pfg : D ⥤ F)
    {U₀ E₀ : A ⥤ D} {U₁ E₁ : B ⥤ E} {U₂ E₂ : C ⥤ F}
    (κf : Sf ⋙ U₁ ≅ U₀ ⋙ Pf) (κg : Sg ⋙ U₂ ≅ U₁ ⋙ Pg)
    (κfg : Sfg ⋙ U₂ ≅ U₀ ⋙ Pfg) (β : Pfg ≅ Pf ⋙ Pg)
    (z₀ : U₀ ≅ E₀) (z₁ : U₁ ≅ E₁) (z₂ : U₂ ≅ E₂)
    (h : ∀ x, κfg.hom.app x ≫ β.hom.app (U₀.obj x) =
      (eqToHom (congrArg (fun S => S ⋙ U₂) hS)).app x ≫
        κg.hom.app (Sf.obj x) ≫ Pg.map (κf.hom.app x)) :
    ∀ x, (rebaseComparison Sfg Pfg κfg z₀ z₂).hom.app x ≫ β.hom.app (E₀.obj x) =
      (eqToHom (congrArg (fun S => S ⋙ E₂) hS)).app x ≫
        (rebaseComparison Sg Pg κg z₁ z₂).hom.app (Sf.obj x) ≫
          Pg.map ((rebaseComparison Sf Pf κf z₀ z₁).hom.app x) := by
  subst Sfg
  intro x
  simp only [eqToHom_refl, NatTrans.id_app, Category.id_comp] at h ⊢
  simp only [rebaseComparison, Iso.trans_hom, Iso.symm_hom, isoWhiskerLeft_hom,
    isoWhiskerRight_hom, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
    Functor.map_comp, Category.assoc]
  rw [← Pg.map_comp_assoc, Iso.hom_inv_id_app, Pg.map_id, Category.id_comp]
  rw [β.hom.naturality, reassoc_of% h x]
  rfl

universe v w v' w'
private theorem liftedComparison_comp_app
    {C : Type v} [Category.{w} C]
    (F : Pseudofunctor (LocallyDiscrete C) Cat.{w', v'})
    {a b c : C} (f : a ⟶ b) (g : b ⟶ c)
    {Nf : F.obj ⟨a⟩ ⥤ F.obj ⟨b⟩} {Ng : F.obj ⟨b⟩ ⥤ F.obj ⟨c⟩}
    {Nfg : F.obj ⟨a⟩ ⥤ F.obj ⟨c⟩}
    (nf : (F.map f.toLoc).toFunctor ≅ Nf) (ng : (F.map g.toLoc).toFunctor ≅ Ng)
    (nfg : (F.map (f ≫ g).toLoc).toFunctor ≅ Nfg)
    (x : Quillen.CategoryTheory.StrictSections.underCocartesian
      (Pseudofunctor.Grothendieck.forget F) a) :
    (smallCoefficientIso F (f ≫ g) nfg).hom.app x ≫
      (smallCoefficientCompIso F f g nf ng nfg).hom.app
        ((Quillen.CategoryTheory.GrothendieckSections.originalEvaluation F a ⋙ AsSmall.up).obj x) =
    (eqToHom (congrArg (fun S => S ⋙
        (Quillen.CategoryTheory.GrothendieckSections.originalEvaluation F c ⋙ AsSmall.up))
      (Quillen.CategoryTheory.StrictSections.underCocartesianReindex_comp
        (Pseudofunctor.Grothendieck.forget F) f g))).app x ≫
      (smallCoefficientIso F g ng).hom.app
        ((Quillen.CategoryTheory.StrictSections.underCocartesianReindex
          (Pseudofunctor.Grothendieck.forget F) f).obj x) ≫
      (smallModelFunctor Ng).map ((smallCoefficientIso F f nf).hom.app x) := by
  have h := NatTrans.congr_app (smallCoefficientIso_comp_hom F f g nf ng nfg) x
  simpa only [smallCoefficientRouteIso, Iso.trans_hom, Iso.symm_hom,
    isoWhiskerLeft_hom, isoWhiskerRight_hom, NatTrans.comp_app, whiskerLeft_app,
    whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id] using h


private def transportComparison
    {A B D E : Type*} [Category A] [Category B] [Category D] [Category E]
    (S : A ⥤ B) {U U' : A ⥤ D} {V V' : B ⥤ E} {P P' : D ⥤ E}
    (hU : U = U') (hV : V = V') (hP : P = P') (κ : S ⋙ V' ≅ U' ⋙ P') :
    S ⋙ V ≅ U ⋙ P :=
  eqToIso (congrArg (fun V => S ⋙ V) hV) ≪≫ κ ≪≫
    eqToIso (congrArg₂ (fun U P => U ⋙ P) hU hP).symm

/-- Transport a composition isomorphism along the displayed functor equalities. -/
def CoefficientSectionEvaluationComposition.transportCompIso
    {D E F : Type*} [Category D] [Category E] [Category F]
    {Pf Pf' : D ⥤ E} {Pg Pg' : E ⥤ F} {Pfg Pfg' : D ⥤ F}
    (hf : Pf = Pf') (hg : Pg = Pg') (hfg : Pfg = Pfg') (β : Pfg' ≅ Pf' ⋙ Pg') :
    Pfg ≅ Pf ⋙ Pg :=
  eqToIso hfg ≪≫ β ≪≫ eqToIso (congrArg₂ (fun P Q => P ⋙ Q) hf hg).symm

open CoefficientSectionEvaluationComposition

private theorem transportComparison_pasting
    {A B C D E F : Type*} [Category A] [Category B] [Category C]
    [Category D] [Category E] [Category F]
    (Sf : A ⥤ B) (Sg : B ⥤ C) (Sfg : A ⥤ C) (hS : Sfg = Sf ⋙ Sg)
    {Pf Pf' : D ⥤ E} {Pg Pg' : E ⥤ F} {Pfg Pfg' : D ⥤ F}
    {U₀ U₀' : A ⥤ D} {U₁ U₁' : B ⥤ E} {U₂ U₂' : C ⥤ F}
    (hf : Pf = Pf') (hg : Pg = Pg') (hfg : Pfg = Pfg')
    (h₀ : U₀ = U₀') (h₁ : U₁ = U₁') (h₂ : U₂ = U₂')
    (κf : Sf ⋙ U₁' ≅ U₀' ⋙ Pf') (κg : Sg ⋙ U₂' ≅ U₁' ⋙ Pg')
    (κfg : Sfg ⋙ U₂' ≅ U₀' ⋙ Pfg') (β : Pfg' ≅ Pf' ⋙ Pg')
    (h : ∀ x, κfg.hom.app x ≫ β.hom.app (U₀'.obj x) =
      (eqToHom (congrArg (fun S => S ⋙ U₂') hS)).app x ≫
        κg.hom.app (Sf.obj x) ≫ Pg'.map (κf.hom.app x)) :
    ∀ x, (transportComparison Sfg h₀ h₂ hfg κfg).hom.app x ≫
        (transportCompIso hf hg hfg β).hom.app (U₀.obj x) =
      (eqToHom (congrArg (fun S => S ⋙ U₂) hS)).app x ≫
        (transportComparison Sg h₁ h₂ hg κg).hom.app (Sf.obj x) ≫
          Pg.map ((transportComparison Sf h₀ h₁ hf κf).hom.app x) := by
  subst Pf'
  subst Pg'
  subst Pfg'
  subst U₀'
  subst U₁'
  subst U₂'
  simpa only [transportComparison, transportCompIso, eqToIso_refl, Iso.refl_trans,
    Iso.trans_refl] using h


/-- The full component equation stays explicit while native functor identities are transported. -/
private def comparisonPasting
    {A B C D E F : Type*} [Category A] [Category B] [Category C]
    [Category D] [Category E] [Category F]
    (Sf : A ⥤ B) (Sg : B ⥤ C) (Sfg : A ⥤ C) (hS : Sfg = Sf ⋙ Sg)
    (U₀ : A ⥤ D) (U₁ : B ⥤ E) (U₂ : C ⥤ F)
    (Pf : D ⥤ E) (Pg : E ⥤ F) (Pfg : D ⥤ F)
    (κf : Sf ⋙ U₁ ≅ U₀ ⋙ Pf) (κg : Sg ⋙ U₂ ≅ U₁ ⋙ Pg)
    (κfg : Sfg ⋙ U₂ ≅ U₀ ⋙ Pfg) (β : Pfg ≅ Pf ⋙ Pg) : Prop :=
  ∀ x, κfg.hom.app x ≫ β.hom.app (U₀.obj x) =
    (eqToHom (congrArg (fun S => S ⋙ U₂) hS)).app x ≫
      κg.hom.app (Sf.obj x) ≫ Pg.map (κf.hom.app x)

open Quillen.CategoryTheory.StrictSections Quillen.CategoryTheory.GrothendieckSections in
private theorem smallCoefficientTransport_pasting
    {C : Type v} [Category.{w} C]
    (F : Pseudofunctor (LocallyDiscrete C) Cat.{w', v'})
    {i j k : C} (f : i ⟶ j) (g : j ⟶ k)
    {Nf : F.obj ⟨i⟩ ⥤ F.obj ⟨j⟩} {Ng : F.obj ⟨j⟩ ⥤ F.obj ⟨k⟩}
    {Nfg : F.obj ⟨i⟩ ⥤ F.obj ⟨k⟩}
    (nf : (F.map f.toLoc).toFunctor ≅ Nf) (ng : (F.map g.toLoc).toFunctor ≅ Ng)
    (nfg : (F.map (f ≫ g).toLoc).toFunctor ≅ Nfg)
    (U₀ : underCocartesian (Pseudofunctor.Grothendieck.forget F) i ⥤ Quillen.Waldhausen.SmallModel
      (F.obj ⟨i⟩))
    (U₁ : underCocartesian (Pseudofunctor.Grothendieck.forget F) j ⥤ Quillen.Waldhausen.SmallModel
      (F.obj ⟨j⟩))
    (U₂ : underCocartesian (Pseudofunctor.Grothendieck.forget F) k ⥤ Quillen.Waldhausen.SmallModel
      (F.obj ⟨k⟩))
    (Pf : Quillen.Waldhausen.SmallModel (F.obj ⟨i⟩) ⥤ Quillen.Waldhausen.SmallModel (F.obj ⟨j⟩))
    (Pg : Quillen.Waldhausen.SmallModel (F.obj ⟨j⟩) ⥤ Quillen.Waldhausen.SmallModel (F.obj ⟨k⟩))
    (Pfg : Quillen.Waldhausen.SmallModel (F.obj ⟨i⟩) ⥤ Quillen.Waldhausen.SmallModel (F.obj ⟨k⟩))
    (h₀ : U₀ = originalEvaluation F i ⋙ AsSmall.up.{w', v', 0})
    (h₁ : U₁ = originalEvaluation F j ⋙ AsSmall.up.{w', v', 0})
    (h₂ : U₂ = originalEvaluation F k ⋙ AsSmall.up.{w', v', 0})
    (hf : Pf = smallModelFunctor Nf) (hg : Pg = smallModelFunctor Ng)
    (hfg : Pfg = smallModelFunctor Nfg)
    (x : underCocartesian (Pseudofunctor.Grothendieck.forget F) i) :
    (transportComparison (underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) (f ≫ g))
      h₀ h₂ hfg (smallCoefficientIso F (f ≫ g) nfg)).hom.app x ≫
        (transportCompIso hf hg hfg (smallCoefficientCompIso F f g nf ng nfg)).hom.app (U₀.obj x) =
      (eqToHom (congrArg (fun S => S ⋙ U₂)
        (underCocartesianReindex_comp (Pseudofunctor.Grothendieck.forget F) f g))).app x ≫
      (transportComparison (underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) g)
        h₁ h₂ hg (smallCoefficientIso F g ng)).hom.app
          ((underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) f).obj x) ≫
      Pg.map ((transportComparison (underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) f)
        h₀ h₁ hf (smallCoefficientIso F f nf)).hom.app x) := by
  exact transportComparison_pasting
    (underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) f)
    (underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) g)
    (underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) (f ≫ g))
    (underCocartesianReindex_comp (Pseudofunctor.Grothendieck.forget F) f g)
    hf hg hfg h₀ h₁ h₂ (smallCoefficientIso F f nf) (smallCoefficientIso F g ng)
    (smallCoefficientIso F (f ≫ g) nfg) (smallCoefficientCompIso F f g nf ng nfg)
    (fun y => liftedComparison_comp_app F f g nf ng nfg y) x

open Quillen.CategoryTheory.StrictSections Quillen.CategoryTheory.GrothendieckSections in
private theorem smallCoefficientTransportPasting
    {C : Type v} [Category.{w} C]
    (F : Pseudofunctor (LocallyDiscrete C) Cat.{w', v'})
    {i j k : C} (f : i ⟶ j) (g : j ⟶ k)
    {Nf : F.obj ⟨i⟩ ⥤ F.obj ⟨j⟩} {Ng : F.obj ⟨j⟩ ⥤ F.obj ⟨k⟩}
    {Nfg : F.obj ⟨i⟩ ⥤ F.obj ⟨k⟩}
    (nf : (F.map f.toLoc).toFunctor ≅ Nf) (ng : (F.map g.toLoc).toFunctor ≅ Ng)
    (nfg : (F.map (f ≫ g).toLoc).toFunctor ≅ Nfg)
    (U₀ : underCocartesian (Pseudofunctor.Grothendieck.forget F) i ⥤ Quillen.Waldhausen.SmallModel
      (F.obj ⟨i⟩))
    (U₁ : underCocartesian (Pseudofunctor.Grothendieck.forget F) j ⥤ Quillen.Waldhausen.SmallModel
      (F.obj ⟨j⟩))
    (U₂ : underCocartesian (Pseudofunctor.Grothendieck.forget F) k ⥤ Quillen.Waldhausen.SmallModel
      (F.obj ⟨k⟩))
    (Pf : Quillen.Waldhausen.SmallModel (F.obj ⟨i⟩) ⥤ Quillen.Waldhausen.SmallModel (F.obj ⟨j⟩))
    (Pg : Quillen.Waldhausen.SmallModel (F.obj ⟨j⟩) ⥤ Quillen.Waldhausen.SmallModel (F.obj ⟨k⟩))
    (Pfg : Quillen.Waldhausen.SmallModel (F.obj ⟨i⟩) ⥤ Quillen.Waldhausen.SmallModel (F.obj ⟨k⟩))
    (h₀ : U₀ = originalEvaluation F i ⋙ AsSmall.up.{w', v', 0})
    (h₁ : U₁ = originalEvaluation F j ⋙ AsSmall.up.{w', v', 0})
    (h₂ : U₂ = originalEvaluation F k ⋙ AsSmall.up.{w', v', 0})
    (hf : Pf = smallModelFunctor Nf) (hg : Pg = smallModelFunctor Ng)
    (hfg : Pfg = smallModelFunctor Nfg)
    : comparisonPasting
      (underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) f)
      (underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) g)
      (underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) (f ≫ g))
      (underCocartesianReindex_comp (Pseudofunctor.Grothendieck.forget F) f g)
      U₀ U₁ U₂ Pf Pg Pfg
      (transportComparison (underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) f)
        h₀ h₁ hf (smallCoefficientIso F f nf))
      (transportComparison (underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) g)
        h₁ h₂ hg (smallCoefficientIso F g ng))
      (transportComparison (underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) (f ≫ g))
        h₀ h₂ hfg (smallCoefficientIso F (f ≫ g) nfg))
      (transportCompIso hf hg hfg (smallCoefficientCompIso F f g nf ng nfg)) := by
  intro x
  exact smallCoefficientTransport_pasting F f g nf ng nfg U₀ U₁ U₂ Pf Pg Pfg h₀ h₁ h₂ hf hg hfg x


private theorem transportComparison_heq
    {A B D E : Type*} [Category A] [Category B] [Category D] [Category E]
    (S : A ⥤ B) {U U' : A ⥤ D} {V V' : B ⥤ E} {P P' : D ⥤ E}
    (hU : U = U') (hV : V = V') (hP : P = P') (κ : S ⋙ V' ≅ U' ⋙ P') :
    HEq (transportComparison S hU hV hP κ) κ := by
  subst U'
  subst V'
  subst P'
  simp only [transportComparison, eqToIso_refl, Iso.refl_trans, Iso.trans_refl, heq_eq_eq]

private theorem rebaseComparisonPasting
    {A B C D E F : Type*} [Category A] [Category B] [Category C]
    [Category D] [Category E] [Category F]
    (Sf : A ⥤ B) (Sg : B ⥤ C) (Sfg : A ⥤ C) (hS : Sfg = Sf ⋙ Sg)
    (Pf : D ⥤ E) (Pg : E ⥤ F) (Pfg : D ⥤ F)
    {U₀ E₀ : A ⥤ D} {U₁ E₁ : B ⥤ E} {U₂ E₂ : C ⥤ F}
    (κf : Sf ⋙ U₁ ≅ U₀ ⋙ Pf) (κg : Sg ⋙ U₂ ≅ U₁ ⋙ Pg)
    (κfg : Sfg ⋙ U₂ ≅ U₀ ⋙ Pfg) (β : Pfg ≅ Pf ⋙ Pg)
    (z₀ : U₀ ≅ E₀) (z₁ : U₁ ≅ E₁) (z₂ : U₂ ≅ E₂)
    (h : comparisonPasting Sf Sg Sfg hS U₀ U₁ U₂ Pf Pg Pfg κf κg κfg β) :
    comparisonPasting Sf Sg Sfg hS E₀ E₁ E₂ Pf Pg Pfg
      (rebaseComparison Sf Pf κf z₀ z₁) (rebaseComparison Sg Pg κg z₁ z₂)
      (rebaseComparison Sfg Pfg κfg z₀ z₂) β :=
  rebaseComparison_pasting Sf Sg Sfg hS Pf Pg Pfg κf κg κfg β z₀ z₁ z₂ h

private def comparisonTargetIso
    {A D E F : Type*} [Category A] [Category D] [Category E] [Category F]
    (U : A ⥤ D) (Pf : D ⥤ E) (Pg : E ⥤ F) (Pfg : D ⥤ F)
    (β : Pfg ≅ Pf ⋙ Pg) : U ⋙ Pfg ≅ (U ⋙ Pf) ⋙ Pg :=
  isoWhiskerLeft U β ≪≫ (Functor.associator U Pf Pg).symm

private def comparisonFirstRouteIso
    {A B C E F : Type*} [Category A] [Category B] [Category C] [Category E] [Category F]
    (Sf : A ⥤ B) (Sg : B ⥤ C) (Sfg : A ⥤ C) (hS : Sfg = Sf ⋙ Sg)
    (U₁ : B ⥤ E) (U₂ : C ⥤ F) (Pg : E ⥤ F)
    (κg : Sg ⋙ U₂ ≅ U₁ ⋙ Pg) : Sfg ⋙ U₂ ≅ (Sf ⋙ U₁) ⋙ Pg :=
  eqToIso (congrArg (fun S => S ⋙ U₂) hS) ≪≫ Functor.associator Sf Sg U₂ ≪≫
    isoWhiskerLeft Sf κg ≪≫ (Functor.associator Sf U₁ Pg).symm

private theorem comparisonPasting_hom
    {A B C D E F : Type*} [Category A] [Category B] [Category C]
    [Category D] [Category E] [Category F]
    (Sf : A ⥤ B) (Sg : B ⥤ C) (Sfg : A ⥤ C) (hS : Sfg = Sf ⋙ Sg)
    (U₀ : A ⥤ D) (U₁ : B ⥤ E) (U₂ : C ⥤ F)
    (Pf : D ⥤ E) (Pg : E ⥤ F) (Pfg : D ⥤ F)
    (κf : Sf ⋙ U₁ ≅ U₀ ⋙ Pf) (κg : Sg ⋙ U₂ ≅ U₁ ⋙ Pg)
    (κfg : Sfg ⋙ U₂ ≅ U₀ ⋙ Pfg) (β : Pfg ≅ Pf ⋙ Pg)
    (h : comparisonPasting Sf Sg Sfg hS U₀ U₁ U₂ Pf Pg Pfg κf κg κfg β) :
    κfg.hom ≫ (comparisonTargetIso U₀ Pf Pg Pfg β).hom =
      (comparisonFirstRouteIso Sf Sg Sfg hS U₁ U₂ Pg κg).hom ≫
        (isoWhiskerRight κf Pg).hom := by
  apply NatTrans.ext
  funext x
  simpa only [comparisonTargetIso, comparisonFirstRouteIso, Iso.trans_hom, Iso.symm_hom,
    isoWhiskerLeft_hom, isoWhiskerRight_hom, NatTrans.comp_app, whiskerLeft_app,
    whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    eqToIso.hom, Category.id_comp, Category.comp_id, Category.assoc] using h x


private theorem transportCompIso_hom_heq
    {D E F : Type*} [Category D] [Category E] [Category F]
    {Pf Pf' : D ⥤ E} {Pg Pg' : E ⥤ F} {Pfg Pfg' : D ⥤ F}
    (hf : Pf = Pf') (hg : Pg = Pg') (hfg : Pfg = Pfg') (β : Pfg' ≅ Pf' ⋙ Pg') :
    HEq (transportCompIso hf hg hfg β).hom β.hom := by
  subst Pf'
  subst Pg'
  subst Pfg'
  simp only [transportCompIso, eqToIso_refl, Iso.refl_trans, Iso.trans_refl, heq_eq_eq]


private theorem comparisonPasting_of_eq
    {A B C D E F : Type*} [Category A] [Category B] [Category C]
    [Category D] [Category E] [Category F]
    {Sf : A ⥤ B} {Sg : B ⥤ C} {Sfg : A ⥤ C} {hS : Sfg = Sf ⋙ Sg}
    {U₀ : A ⥤ D} {U₁ : B ⥤ E} {U₂ : C ⥤ F}
    {Pf : D ⥤ E} {Pg : E ⥤ F} {Pfg : D ⥤ F}
    {κf κf' : Sf ⋙ U₁ ≅ U₀ ⋙ Pf} {κg κg' : Sg ⋙ U₂ ≅ U₁ ⋙ Pg}
    {κfg κfg' : Sfg ⋙ U₂ ≅ U₀ ⋙ Pfg} {β : Pfg ≅ Pf ⋙ Pg}
    (hf : κf = κf') (hg : κg = κg') (hfg : κfg = κfg')
    (h : comparisonPasting Sf Sg Sfg hS U₀ U₁ U₂ Pf Pg Pfg κf' κg' κfg' β) :
    comparisonPasting Sf Sg Sfg hS U₀ U₁ U₂ Pf Pg Pfg κf κg κfg β := by
  cases hf
  cases hg
  cases hfg
  exact h

variable {R : CommRingCat.{u}}

private theorem nativeSmallEvaluation_functor (i : Index R) :
    (boundedFlatCoefficientSectionSmallEquivalence i).functor =
      Quillen.CategoryTheory.GrothendieckSections.originalEvaluation
        (boundedFlatCoefficientPseudofunctor R) i ⋙ AsSmall.up.{u, u + 1, 0} := rfl

theorem CoefficientSectionEvaluationComposition.nativeOriginalModelMap_functor {i j : Index R} (f
  : i ⟶ j) :
    (boundedFlatCoefficientOriginalModelMap f).functor =
      smallModelFunctor
        (boundedFlatNormalizedPullback (Quillen.Scheme.CoefficientBaseChange.map f)) := rfl

private def nativeLiftedIso {i j : Index R} (f : i ⟶ j) :
    boundedFlatCoefficientSectionsMap f ⋙
      (boundedFlatCoefficientSectionSmallEquivalence j).functor ≅
    (boundedFlatCoefficientSectionSmallEquivalence i).functor ⋙
      (boundedFlatCoefficientOriginalModelMap f).functor :=
  transportComparison (boundedFlatCoefficientSectionsMap f)
    (nativeSmallEvaluation_functor i) (nativeSmallEvaluation_functor j)
    (nativeOriginalModelMap_functor f)
    (smallCoefficientIso (boundedFlatCoefficientPseudofunctor R) f
      (boundedFlatPullbackNormalizationIso (Quillen.Scheme.CoefficientBaseChange.map f)))

/-- The actual original target composition, with only equality transports of native functor names.
-/
def boundedFlatCoefficientOriginalModelCompIso {i j k : Index R} (f : i ⟶ j) (g : j ⟶ k) :
    (boundedFlatCoefficientOriginalModelMap (f ≫ g)).functor ≅
      (boundedFlatCoefficientOriginalModelMap f).functor ⋙
        (boundedFlatCoefficientOriginalModelMap g).functor :=
  transportCompIso (nativeOriginalModelMap_functor f) (nativeOriginalModelMap_functor g)
    (nativeOriginalModelMap_functor (f ≫ g))
    (smallCoefficientCompIso (boundedFlatCoefficientPseudofunctor R) f g
      (boundedFlatPullbackNormalizationIso (Quillen.Scheme.CoefficientBaseChange.map f))
      (boundedFlatPullbackNormalizationIso (Quillen.Scheme.CoefficientBaseChange.map g))
      (boundedFlatPullbackNormalizationIso (Quillen.Scheme.CoefficientBaseChange.map (f ≫ g))))

attribute [local irreducible] boundedFlatPerfectPullback boundedFlatPullbackNormalizationIso
  nativeLiftedIso boundedFlatCoefficientOriginalModelCompIso
  boundedFlatCoefficientOriginalModelMap boundedFlatCoefficientSectionSmallEquivalence
  boundedFlatNormalizedPullback smallCoefficientIso smallCoefficientCompIso
  Quillen.CategoryTheory.StrictSections.underCocartesianReindex
  Quillen.CategoryTheory.GrothendieckSections.originalEvaluation

private theorem nativeLiftedIso_pasting {i j k : Index R} (f : i ⟶ j) (g : j ⟶ k) :
    comparisonPasting
      (boundedFlatCoefficientSectionsMap f) (boundedFlatCoefficientSectionsMap g)
      (boundedFlatCoefficientSectionsMap (f ≫ g))
      (Quillen.CategoryTheory.StrictSections.underCocartesianReindex_comp
        (boundedFlatCoefficientProjection R) f g)
      (boundedFlatCoefficientSectionSmallEquivalence i).functor
      (boundedFlatCoefficientSectionSmallEquivalence j).functor
      (boundedFlatCoefficientSectionSmallEquivalence k).functor
      (boundedFlatCoefficientOriginalModelMap f).functor
      (boundedFlatCoefficientOriginalModelMap g).functor
      (boundedFlatCoefficientOriginalModelMap (f ≫ g)).functor
      (nativeLiftedIso f) (nativeLiftedIso g) (nativeLiftedIso (f ≫ g))
      (boundedFlatCoefficientOriginalModelCompIso f g) := by
  unfold nativeLiftedIso boundedFlatCoefficientOriginalModelCompIso
  exact smallCoefficientTransportPasting.{u + 1, u, u + 1, u}
    (boundedFlatCoefficientPseudofunctor R) f g
    (boundedFlatPullbackNormalizationIso (Quillen.Scheme.CoefficientBaseChange.map f))
    (boundedFlatPullbackNormalizationIso (Quillen.Scheme.CoefficientBaseChange.map g))
    (boundedFlatPullbackNormalizationIso (Quillen.Scheme.CoefficientBaseChange.map (f ≫ g)))
    (boundedFlatCoefficientSectionSmallEquivalence i).functor
    (boundedFlatCoefficientSectionSmallEquivalence j).functor
    (boundedFlatCoefficientSectionSmallEquivalence k).functor
    (boundedFlatCoefficientOriginalModelMap f).functor
    (boundedFlatCoefficientOriginalModelMap g).functor
    (boundedFlatCoefficientOriginalModelMap (f ≫ g)).functor
    (nativeSmallEvaluation_functor i) (nativeSmallEvaluation_functor j)
    (nativeSmallEvaluation_functor k) (nativeOriginalModelMap_functor f)
    (nativeOriginalModelMap_functor g) (nativeOriginalModelMap_functor (f ≫ g))


attribute [local semireducible] boundedFlatCoefficientOriginalModelMap
  boundedFlatCoefficientSectionSmallEquivalence boundedFlatNormalizedPullback
  Quillen.CategoryTheory.StrictSections.underCocartesianReindex
  Quillen.CategoryTheory.GrothendieckSections.originalEvaluation

private theorem nativeLiftedIso_eq {i j : Index R} (f : i ⟶ j) :
    nativeLiftedIso f =
      (Functor.associator (boundedFlatCoefficientSectionsMap f)
        (boundedFlatCoefficientOriginalEvaluation j) AsSmall.up).symm ≪≫
      smallModelWhiskerIso (boundedFlatCoefficientOriginalEvaluation i)
        (boundedFlatCoefficientSectionsMap f ⋙ boundedFlatCoefficientOriginalEvaluation j)
        (boundedFlatPerfectPullback (Quillen.Scheme.CoefficientBaseChange.map f))
        (boundedFlatNormalizedPullback (Quillen.Scheme.CoefficientBaseChange.map f))
        (boundedFlatCoefficientSectionReindexIso f)
        (boundedFlatPullbackNormalizationIso (Quillen.Scheme.CoefficientBaseChange.map f)) := by
  unfold nativeLiftedIso
  apply eq_of_heq
  exact (transportComparison_heq (boundedFlatCoefficientSectionsMap f)
    (nativeSmallEvaluation_functor i) (nativeSmallEvaluation_functor j)
    (nativeOriginalModelMap_functor f) _).trans (heq_of_eq
      (smallCoefficientIso_eq (boundedFlatCoefficientPseudofunctor R) f
        (boundedFlatPullbackNormalizationIso (Quillen.Scheme.CoefficientBaseChange.map f))))

attribute [local irreducible] boundedFlatCoefficientOriginalEvaluation
attribute [local semireducible] boundedFlatPullbackNormalizationIso

-- Name the unchanged proposition so default type lint checks its compact interface.
private def nativeEvaluationIsoEquality {i j : Index R} (f : i ⟶ j) : Prop :=
  boundedFlatCoefficientSectionEvaluationIso f =
    rebaseComparison (boundedFlatCoefficientSectionsMap f)
      (boundedFlatCoefficientOriginalModelMap f).functor (nativeLiftedIso f)
      (boundedFlatCoefficientSectionEvaluationNormalizationIso i)
      (boundedFlatCoefficientSectionEvaluationNormalizationIso j)

private theorem nativeEvaluationIso_eq {i j : Index R} (f : i ⟶ j) :
    nativeEvaluationIsoEquality f := by
  unfold nativeEvaluationIsoEquality
  simp only [rebaseComparison, nativeLiftedIso_eq]
  unfold boundedFlatCoefficientSectionEvaluationIso
  dsimp only [id]
  simp only [Iso.trans_assoc]
  dsimp only [boundedFlatPullbackNormalizationIso, boundedFlatNormalizedPullback,
    boundedFlatCoefficientOriginalModelMap, modelMap]

attribute [local irreducible] comparisonPasting boundedFlatCoefficientSectionEvaluationIso
  boundedFlatCoefficientSectionEvaluationModelMap boundedFlatCoefficientOriginalModelMap
  boundedFlatCoefficientSectionSmallEquivalence rebaseComparison

-- Name the unchanged proposition so default type lint checks its compact interface.
private def nativeEvaluationIsoPasting {i j k : Index R} (f : i ⟶ j) (g : j ⟶ k) : Prop :=
  comparisonPasting
    (boundedFlatCoefficientSectionsMap f) (boundedFlatCoefficientSectionsMap g)
    (boundedFlatCoefficientSectionsMap (f ≫ g))
    (Quillen.CategoryTheory.StrictSections.underCocartesianReindex_comp
      (boundedFlatCoefficientProjection R) f g)
    (boundedFlatCoefficientSectionEvaluationModelMap i).functor
    (boundedFlatCoefficientSectionEvaluationModelMap j).functor
    (boundedFlatCoefficientSectionEvaluationModelMap k).functor
    (boundedFlatCoefficientOriginalModelMap f).functor
    (boundedFlatCoefficientOriginalModelMap g).functor
    (boundedFlatCoefficientOriginalModelMap (f ≫ g)).functor
    (boundedFlatCoefficientSectionEvaluationIso f)
    (boundedFlatCoefficientSectionEvaluationIso g)
    (boundedFlatCoefficientSectionEvaluationIso (f ≫ g))
    (boundedFlatCoefficientOriginalModelCompIso f g)

private theorem nativeEvaluationIso_pasting {i j k : Index R} (f : i ⟶ j) (g : j ⟶ k) :
    nativeEvaluationIsoPasting f g := by
  unfold nativeEvaluationIsoPasting
  apply comparisonPasting_of_eq (nativeEvaluationIso_eq f) (nativeEvaluationIso_eq g)
    (nativeEvaluationIso_eq (f ≫ g))
  exact rebaseComparisonPasting
    (boundedFlatCoefficientSectionsMap f) (boundedFlatCoefficientSectionsMap g)
    (boundedFlatCoefficientSectionsMap (f ≫ g))
    (Quillen.CategoryTheory.StrictSections.underCocartesianReindex_comp
      (boundedFlatCoefficientProjection R) f g)
    (boundedFlatCoefficientOriginalModelMap f).functor
    (boundedFlatCoefficientOriginalModelMap g).functor
    (boundedFlatCoefficientOriginalModelMap (f ≫ g)).functor
    (nativeLiftedIso f) (nativeLiftedIso g) (nativeLiftedIso (f ≫ g))
    (boundedFlatCoefficientOriginalModelCompIso f g)
    (boundedFlatCoefficientSectionEvaluationNormalizationIso i)
    (boundedFlatCoefficientSectionEvaluationNormalizationIso j)
    (boundedFlatCoefficientSectionEvaluationNormalizationIso k)
    (nativeLiftedIso_pasting f g)

attribute [local semireducible] boundedFlatCoefficientOriginalModelMap
  boundedFlatCoefficientSectionEvaluationModelMap

open CategoryTheory.Bicategory Quillen.CategoryTheory.GrothendieckSections

private theorem nativePseudofunctor_mapComp_hom {i j k : Index R}
    (f : i ⟶ j) (g : j ⟶ k) :
    ((boundedFlatCoefficientPseudofunctor R).mapComp f.toLoc g.toLoc).hom.toNatTrans =
      eqToHom (congrArg boundedFlatPerfectPullback
        (Quillen.Scheme.CoefficientBaseChange.map_comp f g)) ≫
      (boundedFlatPerfectPullbackCompIso (Quillen.Scheme.CoefficientBaseChange.map g)
        (Quillen.Scheme.CoefficientBaseChange.map f)).hom := by
  simp only [boundedFlatCoefficientPseudofunctor, Pseudofunctor.comp_mapComp,
    Iso.trans_hom, Cat.Hom.toNatTrans_comp, PrelaxFunctor.map₂Iso_hom,
    Functor.toPseudofunctor_mapComp]
  dsimp only [Quiver.Hom.toLoc]
  simp only [eqToIso.hom, PrelaxFunctor.map₂_eqToHom, Cat.Hom₂.eqToHom_toNatTrans]
  rfl

private theorem nativeNormalization_transport {X Y : Scheme.{u}} {f g : X ⟶ Y}
    (h : f = g) :
    (boundedFlatPullbackNormalizationIso f).inv ≫
      eqToHom (congrArg boundedFlatPerfectPullback h) =
    eqToHom (congrArg boundedFlatNormalizedPullback h) ≫
      (boundedFlatPullbackNormalizationIso g).inv := by
  subst h
  simp

/-- Joint coefficient composition retains the original geometric equality and zero paths. -/
def boundedFlatCoefficientNormalizedCompIso {i j k : Index R} (f : i ⟶ j) (g : j ⟶ k) :
    boundedFlatNormalizedPullback (Quillen.Scheme.CoefficientBaseChange.map (f ≫ g)) ≅
    boundedFlatNormalizedPullback (Quillen.Scheme.CoefficientBaseChange.map f) ⋙
      boundedFlatNormalizedPullback (Quillen.Scheme.CoefficientBaseChange.map g) :=
  normalizedCoefficientCompIso (boundedFlatCoefficientPseudofunctor R) f g
    (boundedFlatPullbackNormalizationIso (Quillen.Scheme.CoefficientBaseChange.map f))
    (boundedFlatPullbackNormalizationIso (Quillen.Scheme.CoefficientBaseChange.map g))
    (boundedFlatPullbackNormalizationIso (Quillen.Scheme.CoefficientBaseChange.map (f ≫ g)))

private theorem nativeNormalizedCompIso_hom {i j k : Index R} (f : i ⟶ j) (g : j ⟶ k) :
    (boundedFlatCoefficientNormalizedCompIso f g).hom =
    eqToHom (congrArg boundedFlatNormalizedPullback
      (Quillen.Scheme.CoefficientBaseChange.map_comp f g)) ≫
      (boundedFlatNormalizedPullbackCompIso (Quillen.Scheme.CoefficientBaseChange.map g)
        (Quillen.Scheme.CoefficientBaseChange.map f)).hom := by
  simp only [boundedFlatCoefficientNormalizedCompIso, normalizedCoefficientCompIso,
    boundedFlatNormalizedPullbackCompIso, Iso.trans_hom, Iso.symm_hom,
    Cat.Hom.toNatIso_hom, nativePseudofunctor_mapComp_hom,
    isoWhiskerRight_hom, isoWhiskerLeft_hom, Category.assoc]
  rw [reassoc_of% nativeNormalization_transport
    (Quillen.Scheme.CoefficientBaseChange.map_comp f g)]
  rfl

/-- The actual binary target transformation whiskered by the normalized evaluation. -/
def boundedFlatCoefficientSectionModelTargetIso {i j k : Index R} (f : i ⟶ j) (g : j ⟶ k) :
    (boundedFlatCoefficientSectionEvaluationModelMap i).functor ⋙
      (boundedFlatCoefficientOriginalModelMap (f ≫ g)).functor ≅
    ((boundedFlatCoefficientSectionEvaluationModelMap i).functor ⋙
      (boundedFlatCoefficientOriginalModelMap f).functor) ⋙
        (boundedFlatCoefficientOriginalModelMap g).functor :=
  isoWhiskerLeft (boundedFlatCoefficientSectionEvaluationModelMap i).functor
    (boundedFlatCoefficientOriginalModelCompIso f g) ≪≫
  (Functor.associator (boundedFlatCoefficientSectionEvaluationModelMap i).functor
    (boundedFlatCoefficientOriginalModelMap f).functor
    (boundedFlatCoefficientOriginalModelMap g).functor).symm

/-- Strict source transport followed by the actual second joint evaluation comparison. -/
def boundedFlatCoefficientSectionModelFirstRouteIso {i j k : Index R}
    (f : i ⟶ j) (g : j ⟶ k) :
    (boundedFlatCoefficientSectionModelMap (f ≫ g)).functor ⋙
      (boundedFlatCoefficientSectionEvaluationModelMap k).functor ≅
    ((boundedFlatCoefficientSectionModelMap f).functor ⋙
      (boundedFlatCoefficientSectionEvaluationModelMap j).functor) ⋙
        (boundedFlatCoefficientOriginalModelMap g).functor :=
  eqToIso (congrArg (fun S => S ⋙
    (boundedFlatCoefficientSectionEvaluationModelMap k).functor)
      (Quillen.CategoryTheory.StrictSections.underCocartesianReindex_comp
        (boundedFlatCoefficientProjection R) f g)) ≪≫
  Functor.associator (boundedFlatCoefficientSectionModelMap f).functor
    (boundedFlatCoefficientSectionModelMap g).functor
    (boundedFlatCoefficientSectionEvaluationModelMap k).functor ≪≫
  isoWhiskerLeft (boundedFlatCoefficientSectionModelMap f).functor
    (boundedFlatCoefficientSectionEvaluationIso g) ≪≫
  (Functor.associator (boundedFlatCoefficientSectionModelMap f).functor
    (boundedFlatCoefficientSectionEvaluationModelMap j).functor
    (boundedFlatCoefficientOriginalModelMap g).functor).symm

/-- The actual first joint evaluation comparison followed by the original raw pullback. -/
def boundedFlatCoefficientSectionModelSecondRouteIso {i j k : Index R}
    (f : i ⟶ j) (g : j ⟶ k) :
    ((boundedFlatCoefficientSectionModelMap f).functor ⋙
      (boundedFlatCoefficientSectionEvaluationModelMap j).functor) ⋙
        (boundedFlatCoefficientOriginalModelMap g).functor ≅
    ((boundedFlatCoefficientSectionEvaluationModelMap i).functor ⋙
      (boundedFlatCoefficientOriginalModelMap f).functor) ⋙
        (boundedFlatCoefficientOriginalModelMap g).functor :=
  isoWhiskerRight (boundedFlatCoefficientSectionEvaluationIso f)
    (boundedFlatCoefficientOriginalModelMap g).functor

/-- The two native Model composition routes agree for the actual normalized evaluations. -/
theorem boundedFlatCoefficientSectionModelPasting_hom {i j k : Index R}
    (f : i ⟶ j) (g : j ⟶ k) :
    (boundedFlatCoefficientSectionEvaluationIso (f ≫ g)).hom ≫
      (boundedFlatCoefficientSectionModelTargetIso f g).hom =
    (boundedFlatCoefficientSectionModelFirstRouteIso f g).hom ≫
      (boundedFlatCoefficientSectionModelSecondRouteIso f g).hom := by
  exact comparisonPasting_hom
    (boundedFlatCoefficientSectionsMap f) (boundedFlatCoefficientSectionsMap g)
    (boundedFlatCoefficientSectionsMap (f ≫ g))
    (Quillen.CategoryTheory.StrictSections.underCocartesianReindex_comp
      (boundedFlatCoefficientProjection R) f g)
    (boundedFlatCoefficientSectionEvaluationModelMap i).functor
    (boundedFlatCoefficientSectionEvaluationModelMap j).functor
    (boundedFlatCoefficientSectionEvaluationModelMap k).functor
    (boundedFlatCoefficientOriginalModelMap f).functor
    (boundedFlatCoefficientOriginalModelMap g).functor
    (boundedFlatCoefficientOriginalModelMap (f ≫ g)).functor
    (boundedFlatCoefficientSectionEvaluationIso f) (boundedFlatCoefficientSectionEvaluationIso g)
    (boundedFlatCoefficientSectionEvaluationIso (f ≫ g))
    (boundedFlatCoefficientOriginalModelCompIso f g) (nativeEvaluationIso_pasting f g)

/-- The complete two-parameter native Model composition comparison. -/
def boundedFlatCoefficientSectionModelCompositionRelHomotopy {i j k : Index R}
    (f : i ⟶ j) (g : j ⟶ k) :=
  prespectrumPastingHomotopy
    (V := boundedFlatCoefficientSectionModel i)
    (W := modelOf (boundedFlatPerfectWaldhausen (space k)))
    (F := boundedFlatCoefficientSectionModelMap (f ≫ g) ≫
      boundedFlatCoefficientSectionEvaluationModelMap k)
    (G := boundedFlatCoefficientSectionEvaluationModelMap i ≫
      boundedFlatCoefficientOriginalModelMap (f ≫ g))
    (G' := (boundedFlatCoefficientSectionModelMap f ≫
      boundedFlatCoefficientSectionEvaluationModelMap j) ≫ boundedFlatCoefficientOriginalModelMap g)
    (H := (boundedFlatCoefficientSectionEvaluationModelMap i ≫
      boundedFlatCoefficientOriginalModelMap f) ≫ boundedFlatCoefficientOriginalModelMap g)
    (boundedFlatCoefficientSectionEvaluationIso (f ≫ g)).hom
    (boundedFlatCoefficientSectionModelTargetIso f g).hom
    (boundedFlatCoefficientSectionModelFirstRouteIso f g).hom
    (boundedFlatCoefficientSectionModelSecondRouteIso f g).hom
    (fun _ => (boundedFlatPerfectWaldhausen (space k)).smallModel.weq_iso _ inferInstance)
    (fun _ => (boundedFlatPerfectWaldhausen (space k)).smallModel.weq_iso _ inferInstance)
    (fun _ => (boundedFlatPerfectWaldhausen (space k)).smallModel.weq_iso _ inferInstance)
    (fun _ => (boundedFlatPerfectWaldhausen (space k)).smallModel.weq_iso _ inferInstance)
    (boundedFlatCoefficientSectionModelPasting_hom f g)

private theorem first_route_heq
    {A B C D E : Type*} [Category A] [Category B] [Category C] [Category D] [Category E]
    (J : A ⥤ B) (K : B ⥤ C) (L : A ⥤ C) (P : C ⥤ E)
    (M : B ⥤ D) (N : D ⥤ E) (h : L = J ⋙ K) (η : K ⋙ P ≅ M ⋙ N) :
    HEq ((eqToIso (congrArg (fun S => S ⋙ P) h) ≪≫
      Functor.associator J K P ≪≫ isoWhiskerLeft J η ≪≫
      (Functor.associator J M N).symm).hom) (whiskerLeft J η.hom) := by
  subst h
  apply heq_of_eq
  ext x
  simp

theorem CoefficientSectionEvaluationComposition.nativeFirstRouteHomotopy_level {i j k : Index R}
    (f : i ⟶ j) (g : j ⟶ k) (n : ℕ) :
    (prespectrumTransformationHomotopy
      (V := boundedFlatCoefficientSectionModel i)
      (W := modelOf (boundedFlatPerfectWaldhausen (space k)))
      (F := boundedFlatCoefficientSectionModelMap (f ≫ g) ≫
        boundedFlatCoefficientSectionEvaluationModelMap k)
      (G := (boundedFlatCoefficientSectionModelMap f ≫
        boundedFlatCoefficientSectionEvaluationModelMap j) ≫
          boundedFlatCoefficientOriginalModelMap g)
      (boundedFlatCoefficientSectionModelFirstRouteIso f g).hom
      (fun _ => (boundedFlatPerfectWaldhausen (space k)).smallModel.weq_iso _
        inferInstance)).level n =
    (Homotopy.precomp ((boundedFlatCoefficientSectionPrespectrumFunctor R).map f)
      (boundedFlatCoefficientSectionEvaluationHomotopy g)).level n := by
  have hF : boundedFlatCoefficientSectionModelMap (f ≫ g) ≫
      boundedFlatCoefficientSectionEvaluationModelMap k =
    boundedFlatCoefficientSectionModelMap f ≫ (boundedFlatCoefficientSectionModelMap g ≫
      boundedFlatCoefficientSectionEvaluationModelMap k) :=
    (congrArg (fun S => S ≫ boundedFlatCoefficientSectionEvaluationModelMap k)
      ((boundedFlatCoefficientSectionModelFunctor R).map_comp f g)).trans (Category.assoc _ _ _)
  have hG := Category.assoc (boundedFlatCoefficientSectionModelMap f)
    (boundedFlatCoefficientSectionEvaluationModelMap j) (boundedFlatCoefficientOriginalModelMap g)
  trans (prespectrumTransformationHomotopy
    (F := boundedFlatCoefficientSectionModelMap f ≫ (boundedFlatCoefficientSectionModelMap g ≫
      boundedFlatCoefficientSectionEvaluationModelMap k))
    (G := boundedFlatCoefficientSectionModelMap f ≫
      (boundedFlatCoefficientSectionEvaluationModelMap j ≫
      boundedFlatCoefficientOriginalModelMap g))
    (whiskerLeft (boundedFlatCoefficientSectionModelMap f).functor
      (boundedFlatCoefficientSectionEvaluationIso g).hom)
    (fun _ => (boundedFlatPerfectWaldhausen (space k)).smallModel.weq_iso _ inferInstance)).level n
  · apply prespectrumTransformationHomotopy_level_eq_of_heq hF hG
    exact first_route_heq
      (boundedFlatCoefficientSectionModelMap f).functor
      (boundedFlatCoefficientSectionModelMap g).functor
      (boundedFlatCoefficientSectionModelMap (f ≫ g)).functor
      (boundedFlatCoefficientSectionEvaluationModelMap k).functor
      (boundedFlatCoefficientSectionEvaluationModelMap j).functor
      (boundedFlatCoefficientOriginalModelMap g).functor
      (Quillen.CategoryTheory.StrictSections.underCocartesianReindex_comp
        (boundedFlatCoefficientProjection R) f g) (boundedFlatCoefficientSectionEvaluationIso g)
  · exact prespectrumTransformationHomotopy_precomp_level
      (F := boundedFlatCoefficientSectionModelMap g ≫
        boundedFlatCoefficientSectionEvaluationModelMap k)
      (G := boundedFlatCoefficientSectionEvaluationModelMap j ≫
        boundedFlatCoefficientOriginalModelMap g)
      (boundedFlatCoefficientSectionEvaluationIso g).hom
      (fun _ => (boundedFlatPerfectWaldhausen (space k)).smallModel.weq_iso _ inferInstance)
      (boundedFlatCoefficientSectionModelMap f) n

theorem CoefficientSectionEvaluationComposition.nativeSecondRouteHomotopy_level {i j k : Index R}
    (f : i ⟶ j) (g : j ⟶ k) (n : ℕ) :
    (prespectrumTransformationHomotopy
      (V := boundedFlatCoefficientSectionModel i)
      (W := modelOf (boundedFlatPerfectWaldhausen (space k)))
      (F := (boundedFlatCoefficientSectionModelMap f ≫
        boundedFlatCoefficientSectionEvaluationModelMap j) ≫
          boundedFlatCoefficientOriginalModelMap g)
      (G := (boundedFlatCoefficientSectionEvaluationModelMap i ≫
        boundedFlatCoefficientOriginalModelMap f) ≫ boundedFlatCoefficientOriginalModelMap g)
      (boundedFlatCoefficientSectionModelSecondRouteIso f g).hom
      (fun _ => (boundedFlatPerfectWaldhausen (space k)).smallModel.weq_iso _
        inferInstance)).level n =
    ((boundedFlatCoefficientSectionEvaluationHomotopy f).postcomp
      (boundedFlatPerfectPrespectrumMap (Quillen.Scheme.CoefficientBaseChange.map g))).level n := by
  exact prespectrumTransformationHomotopy_postcomp_level
    (F := boundedFlatCoefficientSectionModelMap f ≫
      boundedFlatCoefficientSectionEvaluationModelMap j)
    (G := boundedFlatCoefficientSectionEvaluationModelMap i ≫
      boundedFlatCoefficientOriginalModelMap f)
    (boundedFlatCoefficientSectionEvaluationIso f).hom
    (fun _ => (boundedFlatPerfectWaldhausen (space j)).smallModel.weq_iso _ inferInstance)
    (boundedFlatCoefficientOriginalModelMap g) n

private theorem small_transport_heq {C D : Type*} [Category C] [Category D]
    {F F' G : C ⥤ D} (h : F = F') (η : F' ⟶ G) :
    HEq (CategoryTheory.Functor.whiskerLeft
        (AsSmall.down : Quillen.Waldhausen.SmallModel C ⥤ C)
        (CategoryTheory.Functor.whiskerRight (eqToHom h ≫ η)
          (AsSmall.up : D ⥤ Quillen.Waldhausen.SmallModel D)))
      (CategoryTheory.Functor.whiskerLeft
        (AsSmall.down : Quillen.Waldhausen.SmallModel C ⥤ C)
        (CategoryTheory.Functor.whiskerRight η
          (AsSmall.up : D ⥤ Quillen.Waldhausen.SmallModel D))) := by
  subst h
  simp only [eqToHom_refl, Category.id_comp]
  rfl

private theorem nativeOriginalCompHomotopy_level {i j k : Index R}
    (f : i ⟶ j) (g : j ⟶ k) (n : ℕ) :
    (prespectrumTransformationHomotopy
      (V := modelOf (boundedFlatPerfectWaldhausen (space i)))
      (W := modelOf (boundedFlatPerfectWaldhausen (space k)))
      (F := boundedFlatCoefficientOriginalModelMap (f ≫ g))
      (G := boundedFlatCoefficientOriginalModelMap f ≫ boundedFlatCoefficientOriginalModelMap g)
      (boundedFlatCoefficientOriginalModelCompIso f g).hom
      (fun _ => (boundedFlatPerfectWaldhausen (space k)).smallModel.weq_iso _
        inferInstance)).level n =
    (boundedFlatNormalizedCompTrack (Quillen.Scheme.CoefficientBaseChange.map g)
      (Quillen.Scheme.CoefficientBaseChange.map f)).level n := by
  rw [boundedFlatNormalizedCompTrack_level]
  apply prespectrumTransformationHomotopy_level_eq_of_heq
  · exact congrArg (fun p => modelMap (boundedFlatPerfectWaldhausen (space i))
      (boundedFlatPerfectWaldhausen (space k)) (boundedFlatNormalizedPullback_exact p)
      (boundedFlatNormalizedPullback_obj_zero p)) (Quillen.Scheme.CoefficientBaseChange.map_comp f
        g)
  · exact (modelMap_comp (boundedFlatPerfectWaldhausen (space i))
      (boundedFlatPerfectWaldhausen (space j)) (boundedFlatPerfectWaldhausen (space k))
      (boundedFlatNormalizedPullback_exact (Quillen.Scheme.CoefficientBaseChange.map f))
      (boundedFlatNormalizedPullback_exact (Quillen.Scheme.CoefficientBaseChange.map g))
      (boundedFlatNormalizedPullback_obj_zero _) (boundedFlatNormalizedPullback_obj_zero _)).symm
  · unfold boundedFlatCoefficientOriginalModelCompIso
    have hβ := transportCompIso_hom_heq
      (nativeOriginalModelMap_functor f) (nativeOriginalModelMap_functor g)
      (nativeOriginalModelMap_functor (f ≫ g))
      (smallCoefficientCompIso (boundedFlatCoefficientPseudofunctor R) f g
        (boundedFlatPullbackNormalizationIso (Quillen.Scheme.CoefficientBaseChange.map f))
        (boundedFlatPullbackNormalizationIso (Quillen.Scheme.CoefficientBaseChange.map g))
        (boundedFlatPullbackNormalizationIso (Quillen.Scheme.CoefficientBaseChange.map (f ≫ g))))
    refine hβ.trans ?_
    unfold smallCoefficientCompIso
    change HEq (whiskerLeft AsSmall.down (whiskerRight
      (boundedFlatCoefficientNormalizedCompIso f g).hom AsSmall.up)) _
    rw [nativeNormalizedCompIso_hom]
    exact small_transport_heq (congrArg boundedFlatNormalizedPullback
      (Quillen.Scheme.CoefficientBaseChange.map_comp f g))
      (boundedFlatNormalizedPullbackCompIso (Quillen.Scheme.CoefficientBaseChange.map g)
        (Quillen.Scheme.CoefficientBaseChange.map f)).hom

private theorem target_route_heq
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (J : A ⥤ B) (F : B ⥤ D) (G : B ⥤ C) (H : C ⥤ D) (η : F ≅ G ⋙ H) :
    HEq ((isoWhiskerLeft J η ≪≫ (Functor.associator J G H).symm).hom)
      (whiskerLeft J η.hom) := by
  apply heq_of_eq
  ext x
  simp

theorem CoefficientSectionEvaluationComposition.nativeTargetHomotopy_level {i j k : Index R}
    (f : i ⟶ j) (g : j ⟶ k) (n : ℕ) :
    (prespectrumTransformationHomotopy
      (V := boundedFlatCoefficientSectionModel i)
      (W := modelOf (boundedFlatPerfectWaldhausen (space k)))
      (F := boundedFlatCoefficientSectionEvaluationModelMap i ≫
        boundedFlatCoefficientOriginalModelMap (f ≫ g))
      (G := (boundedFlatCoefficientSectionEvaluationModelMap i ≫
        boundedFlatCoefficientOriginalModelMap f) ≫ boundedFlatCoefficientOriginalModelMap g)
      (boundedFlatCoefficientSectionModelTargetIso f g).hom
      (fun _ => (boundedFlatPerfectWaldhausen (space k)).smallModel.weq_iso _
        inferInstance)).level n =
    (Homotopy.precomp (boundedFlatCoefficientSectionEvaluationPrespectrumMap i)
      (boundedFlatNormalizedCompTrack (Quillen.Scheme.CoefficientBaseChange.map g)
        (Quillen.Scheme.CoefficientBaseChange.map f))).level n := by
  trans (prespectrumTransformationHomotopy
    (F := boundedFlatCoefficientSectionEvaluationModelMap i ≫
      boundedFlatCoefficientOriginalModelMap (f ≫ g))
    (G := boundedFlatCoefficientSectionEvaluationModelMap i ≫
      (boundedFlatCoefficientOriginalModelMap f ≫ boundedFlatCoefficientOriginalModelMap g))
    (whiskerLeft (boundedFlatCoefficientSectionEvaluationModelMap i).functor
      (boundedFlatCoefficientOriginalModelCompIso f g).hom)
    (fun _ => (boundedFlatPerfectWaldhausen (space k)).smallModel.weq_iso _ inferInstance)).level n
  · apply prespectrumTransformationHomotopy_level_eq_of_heq rfl (Category.assoc _ _ _)
    exact target_route_heq (boundedFlatCoefficientSectionEvaluationModelMap i).functor
      (boundedFlatCoefficientOriginalModelMap (f ≫ g)).functor
      (boundedFlatCoefficientOriginalModelMap f).functor (boundedFlatCoefficientOriginalModelMap
        g).functor
      (boundedFlatCoefficientOriginalModelCompIso f g)
  · rw [prespectrumTransformationHomotopy_precomp_level
      (F := boundedFlatCoefficientOriginalModelMap (f ≫ g))
      (G := boundedFlatCoefficientOriginalModelMap f ≫ boundedFlatCoefficientOriginalModelMap g)
      (boundedFlatCoefficientOriginalModelCompIso f g).hom
      (fun _ => (boundedFlatPerfectWaldhausen (space k)).smallModel.weq_iso _ inferInstance)
      (boundedFlatCoefficientSectionEvaluationModelMap i)]
    apply ContinuousMap.ext
    rintro ⟨s, x⟩
    exact DFunLike.congr_fun (nativeOriginalCompHomotopy_level f g n)
      (s, (boundedFlatCoefficientSectionEvaluationPrespectrumMap i).map n x)

/-- Original evaluation followed by the total normalized native geometric composition. -/
def boundedFlatCoefficientSectionCompositionTotalRoute {i j k : Index R}
    (f : i ⟶ j) (g : j ⟶ k) :
    Homotopy ((boundedFlatCoefficientSectionPrespectrumFunctor R).map (f ≫ g) ≫
      boundedFlatCoefficientSectionEvaluationPrespectrumMap k)
    ((boundedFlatCoefficientSectionEvaluationPrespectrumMap i ≫
      boundedFlatPerfectPrespectrumMap (Quillen.Scheme.CoefficientBaseChange.map f)) ≫
        boundedFlatPerfectPrespectrumMap (Quillen.Scheme.CoefficientBaseChange.map g)) :=
  ((boundedFlatCoefficientSectionEvaluationHomotopy (f ≫ g)).trans
    (Homotopy.precomp (boundedFlatCoefficientSectionEvaluationPrespectrumMap i)
      ((boundedFlatNormalizedCompTrack (Quillen.Scheme.CoefficientBaseChange.map g)
        (Quillen.Scheme.CoefficientBaseChange.map f)).cast
          (congrArg boundedFlatPerfectPrespectrumMap
            (Quillen.Scheme.CoefficientBaseChange.map_comp f g).symm) rfl))).cast
    rfl (Category.assoc _ _ _).symm

/-- Original evaluation followed by the unchanged split geometric composition track. -/
def boundedFlatCoefficientSectionCompositionSplitRoute {i j k : Index R}
    (f : i ⟶ j) (g : j ⟶ k) :
    Homotopy ((boundedFlatCoefficientSectionPrespectrumFunctor R).map (f ≫ g) ≫
      boundedFlatCoefficientSectionEvaluationPrespectrumMap k)
    ((boundedFlatCoefficientSectionEvaluationPrespectrumMap i ≫
      boundedFlatPerfectPrespectrumMap (Quillen.Scheme.CoefficientBaseChange.map f)) ≫
        boundedFlatPerfectPrespectrumMap (Quillen.Scheme.CoefficientBaseChange.map g)) :=
  ((boundedFlatCoefficientSectionEvaluationHomotopy (f ≫ g)).trans
    (Homotopy.precomp (boundedFlatCoefficientSectionEvaluationPrespectrumMap i)
      ((boundedFlatPerfectPrespectrumCompHomotopy (Quillen.Scheme.CoefficientBaseChange.map g)
        (Quillen.Scheme.CoefficientBaseChange.map f)).cast
          (congrArg boundedFlatPerfectPrespectrumMap
            (Quillen.Scheme.CoefficientBaseChange.map_comp f g).symm) rfl))).cast
    rfl (Category.assoc _ _ _).symm

/-- Both original joint evaluation tracks with the prescribed strict source endpoint. -/
def boundedFlatCoefficientSectionCompositionWhiskeredRoute {i j k : Index R}
    (f : i ⟶ j) (g : j ⟶ k) :
    Homotopy ((boundedFlatCoefficientSectionPrespectrumFunctor R).map (f ≫ g) ≫
      boundedFlatCoefficientSectionEvaluationPrespectrumMap k)
    ((boundedFlatCoefficientSectionEvaluationPrespectrumMap i ≫
      boundedFlatPerfectPrespectrumMap (Quillen.Scheme.CoefficientBaseChange.map f)) ≫
        boundedFlatPerfectPrespectrumMap (Quillen.Scheme.CoefficientBaseChange.map g)) :=
  ((Homotopy.precomp ((boundedFlatCoefficientSectionPrespectrumFunctor R).map f)
    (boundedFlatCoefficientSectionEvaluationHomotopy g)).cast
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun S => S ≫ boundedFlatCoefficientSectionEvaluationPrespectrumMap k)
          ((boundedFlatCoefficientSectionPrespectrumFunctor R).map_comp f g).symm))
      (Category.assoc _ _ _).symm).trans
    ((boundedFlatCoefficientSectionEvaluationHomotopy f).postcomp
      (boundedFlatPerfectPrespectrumMap (Quillen.Scheme.CoefficientBaseChange.map g)))

/-- The actual joint composition equation compares both whole original evaluation routes. -/
def boundedFlatCoefficientSectionCompositionRelHomotopy {i j k : Index R}
    (f : i ⟶ j) (g : j ⟶ k) :
    (boundedFlatCoefficientSectionCompositionSplitRoute f g).RelHomotopy
      (boundedFlatCoefficientSectionCompositionWhiskeredRoute f g) := by
  have Js : (boundedFlatCoefficientSectionCompositionTotalRoute f g).RelHomotopy
      (boundedFlatCoefficientSectionCompositionSplitRoute f g) :=
    ((Homotopy.RelHomotopy.refl (boundedFlatCoefficientSectionEvaluationHomotopy (f ≫ g))).hcomp
      (Homotopy.RelHomotopy.precomp (boundedFlatCoefficientSectionEvaluationPrespectrumMap i)
        ((boundedFlatNormalizedCompTrackComparison (Quillen.Scheme.CoefficientBaseChange.map g)
          (Quillen.Scheme.CoefficientBaseChange.map f)).cast
            (congrArg boundedFlatPerfectPrespectrumMap
              (Quillen.Scheme.CoefficientBaseChange.map_comp f g).symm) rfl))).cast
        rfl (Category.assoc _ _ _).symm
  have Jw : (boundedFlatCoefficientSectionCompositionTotalRoute f g).RelHomotopy
      (boundedFlatCoefficientSectionCompositionWhiskeredRoute f g) := by
    apply (boundedFlatCoefficientSectionModelCompositionRelHomotopy f g).ofLevels
    · intro n
      apply Homotopy.trans_level_congr
      · rfl
      · exact (nativeTargetHomotopy_level f g n).symm
    · intro n
      apply Homotopy.trans_level_congr
      · exact (nativeFirstRouteHomotopy_level f g n).symm
      · exact (nativeSecondRouteHomotopy_level f g n).symm
  exact Js.symm.trans Jw


open Quillen.PolynomialBaseChange
variable {P Q : Over (Spec R)} (ι : P ⟶ Q)

/-- The original geometric composition track for a specified native Laurent chart. -/
def boundedFlatCoefficientFullOpenChartGeometricTrack (a : Under R)
    (k : (polynomialUnderFunctor R).obj a ⟶ (laurentUnderFunctor R).obj a)
    (h : (polynomialUnderCoefficient R).app a ≫ k = (laurentUnderCoefficient R).app a) :
    Homotopy (boundedFlatPerfectPrespectrumMap (laurentProjection P a))
      (boundedFlatPerfectPrespectrumMap (polynomialProjection P a) ≫
        boundedFlatPerfectPrespectrumMap (coefficientMap P k)) :=
  (boundedFlatPerfectPrespectrumCompHomotopy (coefficientMap P k) (polynomialProjection P a)).cast
    (congrArg boundedFlatPerfectPrespectrumMap
      ((coefficientMap_comp P ((polynomialUnderCoefficient R).app a) k).symm.trans
        (congrArg (coefficientMap P) h))) rfl

/-- Original Laurent evaluation followed by the unchanged native chart composition track. -/
def boundedFlatCoefficientFullOpenChartOuterTrack (a : Under R)
    (k : (polynomialUnderFunctor R).obj a ⟶ (laurentUnderFunctor R).obj a)
    (h : (polynomialUnderCoefficient R).app a ≫ k = (laurentUnderCoefficient R).app a) :
    Homotopy ((boundedFlatCoefficientFullOpenPrespectrumFunctor ι).map
        ((laurentUnderCoefficient R).app a) ≫
      boundedFlatCoefficientSectionEvaluationPrespectrumMap (op P, (laurentUnderFunctor R).obj a))
    ((boundedFlatCoefficientSectionEvaluationPrespectrumMap (op P, a) ≫
      boundedFlatPerfectPrespectrumMap (polynomialProjection P a)) ≫
        boundedFlatPerfectPrespectrumMap (coefficientMap P k)) :=
  (boundedFlatCoefficientSectionEvaluationHomotopy
    (i := (op P, a)) (k := (op P, (laurentUnderFunctor R).obj a))
    (𝟙 (op P), (laurentUnderCoefficient R).app a)).trans
      ((Homotopy.precomp (boundedFlatCoefficientSectionEvaluationPrespectrumMap (op P, a))
        (boundedFlatCoefficientFullOpenChartGeometricTrack (P := P) a k h)).cast
          rfl (Category.assoc _ _ _).symm)

/-- The actual second coefficient evaluation on the literal strict polynomial source leg. -/
def boundedFlatCoefficientFullOpenChartFirstTrack (a : Under R)
    (k : (polynomialUnderFunctor R).obj a ⟶ (laurentUnderFunctor R).obj a)
    (h : (polynomialUnderCoefficient R).app a ≫ k = (laurentUnderCoefficient R).app a) :
    Homotopy ((boundedFlatCoefficientFullOpenPrespectrumFunctor ι).map
        ((laurentUnderCoefficient R).app a) ≫
      boundedFlatCoefficientSectionEvaluationPrespectrumMap (op P, (laurentUnderFunctor R).obj a))
    (((boundedFlatCoefficientFullOpenPrespectrumFunctor ι).map
        ((polynomialUnderCoefficient R).app a) ≫
      boundedFlatCoefficientSectionEvaluationPrespectrumMap (op P, (polynomialUnderFunctor R).obj
        a)) ≫
        boundedFlatPerfectPrespectrumMap (coefficientMap P k)) :=
  (Homotopy.precomp ((boundedFlatCoefficientFullOpenPrespectrumFunctor ι).map
    ((polynomialUnderCoefficient R).app a))
    (boundedFlatCoefficientSectionEvaluationHomotopy
      (i := (op P, (polynomialUnderFunctor R).obj a))
      (k := (op P, (laurentUnderFunctor R).obj a)) (𝟙 (op P), k))).cast
    ((Category.assoc _ _ _).symm.trans
      (congrArg (fun z => z ≫ boundedFlatCoefficientSectionEvaluationPrespectrumMap
        (op P, (laurentUnderFunctor R).obj a))
        (((boundedFlatCoefficientFullOpenPrespectrumFunctor ι).map_comp
          ((polynomialUnderCoefficient R).app a) k).symm.trans
            (congrArg (boundedFlatCoefficientFullOpenPrespectrumFunctor ι).map h))))
    (Category.assoc _ _ _).symm

/-- The actual first coefficient evaluation followed by the original geometric chart. -/
def boundedFlatCoefficientFullOpenChartSecondTrack (a : Under R)
    (k : (polynomialUnderFunctor R).obj a ⟶ (laurentUnderFunctor R).obj a) :
    Homotopy (((boundedFlatCoefficientFullOpenPrespectrumFunctor ι).map
        ((polynomialUnderCoefficient R).app a) ≫
      boundedFlatCoefficientSectionEvaluationPrespectrumMap (op P, (polynomialUnderFunctor R).obj
        a)) ≫
        boundedFlatPerfectPrespectrumMap (coefficientMap P k))
    ((boundedFlatCoefficientSectionEvaluationPrespectrumMap (op P, a) ≫
      boundedFlatPerfectPrespectrumMap (polynomialProjection P a)) ≫
        boundedFlatPerfectPrespectrumMap (coefficientMap P k)) :=
  (boundedFlatCoefficientSectionEvaluationHomotopy
    (i := (op P, a)) (k := (op P, (polynomialUnderFunctor R).obj a))
    (𝟙 (op P), (polynomialUnderCoefficient R).app a)).postcomp
      (boundedFlatPerfectPrespectrumMap (coefficientMap P k))

/-- Whole level families are retained during specialization, including every homotopy parameter. -/
def CoefficientSectionEvaluationComposition.homotopyLevelsAgree {E F : LoopPrespectrum.{v}}
    {a b a' b' : E ⟶ F} (H : Homotopy a b) (K : Homotopy a' b') : Prop :=
  ∀ n, H.level n = K.level n

private theorem homotopyLevelsAgree_trans {E F : LoopPrespectrum.{v}}
    {a b c a' b' c' : E ⟶ F}
    (H : Homotopy a b) (K : Homotopy b c)
    (H' : Homotopy a' b') (K' : Homotopy b' c')
    (hH : homotopyLevelsAgree H H') (hK : homotopyLevelsAgree K K') :
    homotopyLevelsAgree (H.trans K) (H'.trans K') := by
  intro n
  exact Homotopy.trans_level_congr H K H' K' n (hH n) (hK n)

private theorem homotopyLevelsAgree_cast_right {E F : LoopPrespectrum.{v}}
    {a b a' b' c d : E ⟶ F} {H : Homotopy a b} {K : Homotopy a' b'}
    (p : a' = c) (q : b' = d) (h : homotopyLevelsAgree H K) :
    homotopyLevelsAgree H (K.cast p q) := by
  intro n
  exact h n

private def coefficientEvaluationLevelsAgree {i j : Index R} (f g : i ⟶ j) : Prop :=
  homotopyLevelsAgree (boundedFlatCoefficientSectionEvaluationHomotopy f)
    (boundedFlatCoefficientSectionEvaluationHomotopy g)

private theorem coefficientEvaluationLevelsAgree_of_eq
    {i j : Index R} {f g : i ⟶ j} (h : f = g) :
    coefficientEvaluationLevelsAgree f g := by
  subst h
  intro n
  rfl

theorem CoefficientSectionEvaluationComposition.nativeChartWhiskeredRoute_level (a : Under R)
    (k : (polynomialUnderFunctor R).obj a ⟶ (laurentUnderFunctor R).obj a)
    (h : (polynomialUnderCoefficient R).app a ≫ k = (laurentUnderCoefficient R).app a) (n : ℕ) :
    ((boundedFlatCoefficientFullOpenChartFirstTrack ι a k h).trans
      (boundedFlatCoefficientFullOpenChartSecondTrack ι a k)).level n =
    (boundedFlatCoefficientSectionCompositionWhiskeredRoute
      (i := (op P, a)) (j := (op P, (polynomialUnderFunctor R).obj a))
      (k := (op P, (laurentUnderFunctor R).obj a))
      (𝟙 (op P), (polynomialUnderCoefficient R).app a) (𝟙 (op P), k)).level n := by
  apply Homotopy.trans_level_congr <;> rfl

private theorem nativeChartLaurentEvaluationLevels (a : Under R)
    (k : (polynomialUnderFunctor R).obj a ⟶ (laurentUnderFunctor R).obj a)
    (h : (polynomialUnderCoefficient R).app a ≫ k = (laurentUnderCoefficient R).app a) :
    coefficientEvaluationLevelsAgree
      (i := (op P, a)) (j := (op P, (laurentUnderFunctor R).obj a))
      (𝟙 (op P), (laurentUnderCoefficient R).app a)
      (CategoryStruct.comp (Y := ((op P, (polynomialUnderFunctor R).obj a) : Index R))
        (𝟙 (op P), (polynomialUnderCoefficient R).app a) (𝟙 (op P), k)) := by
  apply coefficientEvaluationLevelsAgree_of_eq
  change (𝟙 (op P), (laurentUnderCoefficient R).app a) =
    (𝟙 (op P) ≫ 𝟙 (op P), (polynomialUnderCoefficient R).app a ≫ k)
  rw [Category.id_comp, h]

private theorem nativeChartGeometricLevels (a : Under R)
    (k : (polynomialUnderFunctor R).obj a ⟶ (laurentUnderFunctor R).obj a)
    (h : (polynomialUnderCoefficient R).app a ≫ k = (laurentUnderCoefficient R).app a) :
    homotopyLevelsAgree
      ((Homotopy.precomp (boundedFlatCoefficientSectionEvaluationPrespectrumMap (op P, a))
      (boundedFlatCoefficientFullOpenChartGeometricTrack (P := P) a k h)).cast
        rfl (Category.assoc _ _ _).symm)
      (Homotopy.precomp (boundedFlatCoefficientSectionEvaluationPrespectrumMap (op P, a))
      ((boundedFlatPerfectPrespectrumCompHomotopy
        (Quillen.Scheme.CoefficientBaseChange.map
          (i := (op P, (polynomialUnderFunctor R).obj a))
          (k := (op P, (laurentUnderFunctor R).obj a)) (𝟙 (op P), k))
        (Quillen.Scheme.CoefficientBaseChange.map
          (i := (op P, a)) (k := (op P, (polynomialUnderFunctor R).obj a))
          (𝟙 (op P), (polynomialUnderCoefficient R).app a))).cast
        (congrArg boundedFlatPerfectPrespectrumMap
          (Quillen.Scheme.CoefficientBaseChange.map_comp
            (i := (op P, a)) (k := (op P, (polynomialUnderFunctor R).obj a))
            (l := (op P, (laurentUnderFunctor R).obj a))
            (𝟙 (op P), (polynomialUnderCoefficient R).app a) (𝟙 (op P), k)).symm) rfl)) := by
  intro n
  rfl

theorem CoefficientSectionEvaluationComposition.nativeChartSplitLevels (a : Under R)
    (k : (polynomialUnderFunctor R).obj a ⟶ (laurentUnderFunctor R).obj a)
    (h : (polynomialUnderCoefficient R).app a ≫ k = (laurentUnderCoefficient R).app a) :
    homotopyLevelsAgree
      (boundedFlatCoefficientFullOpenChartOuterTrack ι a k h)
      (boundedFlatCoefficientSectionCompositionSplitRoute
      (i := (op P, a)) (j := (op P, (polynomialUnderFunctor R).obj a))
      (k := (op P, (laurentUnderFunctor R).obj a))
      (𝟙 (op P), (polynomialUnderCoefficient R).app a) (𝟙 (op P), k)) := by
  unfold boundedFlatCoefficientFullOpenChartOuterTrack
    boundedFlatCoefficientSectionCompositionSplitRoute
  apply homotopyLevelsAgree_cast_right
  exact homotopyLevelsAgree_trans _ _ _ _
    (nativeChartLaurentEvaluationLevels (P := P) a k h)
    (nativeChartGeometricLevels (P := P) a k h)

/-- The joint composition equation supplies the entire actual native chart pasting. -/
def boundedFlatCoefficientFullOpenChartFirstPasting (a : Under R)
    (k : (polynomialUnderFunctor R).obj a ⟶ (laurentUnderFunctor R).obj a)
    (h : (polynomialUnderCoefficient R).app a ≫ k = (laurentUnderCoefficient R).app a) :
    ((boundedFlatCoefficientFullOpenChartFirstTrack ι a k h).trans
      (boundedFlatCoefficientFullOpenChartSecondTrack ι a k)).RelHomotopy
        (boundedFlatCoefficientFullOpenChartOuterTrack ι a k h) :=
  (boundedFlatCoefficientSectionCompositionRelHomotopy
    (i := (op P, a)) (j := (op P, (polynomialUnderFunctor R).obj a))
    (k := (op P, (laurentUnderFunctor R).obj a))
    (𝟙 (op P), (polynomialUnderCoefficient R).app a) (𝟙 (op P), k)).symm.ofLevels
      _ _ (nativeChartWhiskeredRoute_level ι a k h) (nativeChartSplitLevels ι a k h)

/-- The literal source Laurent track followed by unchanged original evaluation. -/
def boundedFlatCoefficientFullOpenBassEvaluationSourceTrack (a : Under R) :=
  (StrictSquare.track (boundedFlatCoefficientFullOpenBassSquare ι a)).postcomp
    (boundedFlatCoefficientSectionEvaluationPrespectrumMap (op P, (laurentUnderFunctor R).obj a))

/-- Both original polynomial evaluation tracks flank the original raw native Bass cylinder. -/
def boundedFlatCoefficientFullOpenBassEvaluationTargetTrack (a : Under R) :=
  ((boundedFlatCoefficientSectionEvaluationHomotopy
    (i := (op P, a)) (k := (op P, (polynomialUnderFunctor R).obj a))
    (𝟙 (op P), (polynomialUnderCoefficient R).app a)).postcomp
      (boundedFlatPerfectPrespectrumMap (laurentPlus P a))).trans
    (((Homotopy.precomp (boundedFlatCoefficientSectionEvaluationPrespectrumMap (op P, a))
      (boundedFlatCoefficientBassSquareHomotopy P a)).cast
        (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm).trans
      ((boundedFlatCoefficientSectionEvaluationHomotopy
        (i := (op P, a)) (k := (op P, (polynomialUnderFunctor R).obj a))
        (𝟙 (op P), (polynomialUnderCoefficient R).app a)).postcomp
          (boundedFlatPerfectPrespectrumMap (laurentMinus P a))).symm)

/-- Original positive-chart evaluation on the literal strict source leg. -/
def boundedFlatCoefficientFullOpenBassEvaluationPlusTrack (a : Under R) :=
  (Homotopy.precomp ((boundedFlatCoefficientFullOpenPrespectrumFunctor ι).map
    ((polynomialUnderCoefficient R).app a))
    (boundedFlatCoefficientSectionEvaluationHomotopy
      (i := (op P, (polynomialUnderFunctor R).obj a))
      (k := (op P, (laurentUnderFunctor R).obj a))
      (𝟙 (op P), (underToLaurent R).app a))).cast
        (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm

/-- The independent inverse chart retains its original evaluation track on that same source leg. -/
def boundedFlatCoefficientFullOpenBassEvaluationMinusTrack (a : Under R) :=
  (Homotopy.precomp ((boundedFlatCoefficientFullOpenPrespectrumFunctor ι).map
    ((polynomialUnderCoefficient R).app a))
    (boundedFlatCoefficientSectionEvaluationHomotopy
      (i := (op P, (polynomialUnderFunctor R).obj a))
      (k := (op P, (laurentUnderFunctor R).obj a))
      (𝟙 (op P), (underToLaurentInvert R).app a))).cast
        (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm

/-- The complete original moving Laurent evaluation boundary. -/
def boundedFlatCoefficientFullOpenBassEvaluationPastedTrack (a : Under R) :=
  ((boundedFlatCoefficientFullOpenBassEvaluationPlusTrack ι a).trans
    (boundedFlatCoefficientFullOpenBassEvaluationTargetTrack (P := P) a)).trans
      (boundedFlatCoefficientFullOpenBassEvaluationMinusTrack ι a).symm

/-- Joint native composition supplies the full original two-chart relative boundary. -/
def boundedFlatCoefficientFullOpenBassEvaluationPasting (a : Under R) :
    (boundedFlatCoefficientFullOpenBassEvaluationSourceTrack ι a).RelHomotopy
      (boundedFlatCoefficientFullOpenBassEvaluationPastedTrack ι a) := by
  let kp := (underToLaurent R).app a
  let km := (underToLaurentInvert R).app a
  let hp := polynomialUnderCoefficient_toLaurent R a
  let hm := polynomialUnderCoefficient_toLaurentInvert R a
  have J := Homotopy.RelHomotopy.pasteStrictSourceSquares
    (T := boundedFlatCoefficientSectionEvaluationHomotopy
      (i := (op P, a)) (k := (op P, (laurentUnderFunctor R).obj a))
      (𝟙 (op P), (laurentUnderCoefficient R).app a))
    (Lp := boundedFlatCoefficientFullOpenChartFirstTrack ι a kp hp)
    (Pp := boundedFlatCoefficientFullOpenChartSecondTrack ι a kp)
    (Kp := (Homotopy.precomp (boundedFlatCoefficientSectionEvaluationPrespectrumMap (op P, a))
      (boundedFlatCoefficientFullOpenChartGeometricTrack (P := P) a kp hp)).cast
        rfl (Category.assoc _ _ _).symm)
    (Lm := boundedFlatCoefficientFullOpenChartFirstTrack ι a km hm)
    (Pm := boundedFlatCoefficientFullOpenChartSecondTrack ι a km)
    (Km := (Homotopy.precomp (boundedFlatCoefficientSectionEvaluationPrespectrumMap (op P, a))
      (boundedFlatCoefficientFullOpenChartGeometricTrack (P := P) a km hm)).cast
        rfl (Category.assoc _ _ _).symm)
    (boundedFlatCoefficientFullOpenChartFirstPasting ι a kp hp)
    (boundedFlatCoefficientFullOpenChartFirstPasting ι a km hm)
  refine J.ofLevels _ _ ?_ ?_
  · intro n
    apply ContinuousMap.ext
    rintro ⟨s, x⟩
    change (((boundedFlatCoefficientFullOpenBassSquare ι a).left.hom ≫
      (boundedFlatCoefficientFullOpenBassSquare ι a).hom.right) ≫
        boundedFlatCoefficientSectionEvaluationPrespectrumMap
          (op P, (laurentUnderFunctor R).obj a)).map n x = _
    exact congrArg (fun z =>
      (z ≫ boundedFlatCoefficientSectionEvaluationPrespectrumMap
        (op P, (laurentUnderFunctor R).obj a)).map n x)
      (Quillen.KTheory.Bass.LaurentSeed.square_source
        (boundedFlatCoefficientFullOpenPrespectrumFunctor ι) a)
  · intro n
    apply Homotopy.trans_level_congr
    · apply Homotopy.trans_level_congr
      · rfl
      · apply Homotopy.trans_level_congr
        · rfl
        · apply Homotopy.trans_level_congr
          · simp only [Homotopy.cast_level, boundedFlatCoefficientBassSquareHomotopy,
              Homotopy.precomp_trans, Homotopy.precomp_symm]
            apply Homotopy.trans_level_congr <;> rfl
          · rfl
    · rfl

/-- Regroup the original source-cylinder endpoints for actual quotient descent. -/
def boundedFlatCoefficientFullOpenBassEvaluationSourceDescTrack (a : Under R) :=
  (boundedFlatCoefficientFullOpenBassEvaluationSourceTrack ι a).cast
    (Category.assoc _ _ _) (Category.assoc _ _ _)

/-- Regroup the original raw/native target-cylinder endpoints for actual quotient descent. -/
def boundedFlatCoefficientFullOpenBassEvaluationTargetDescTrack (a : Under R) :=
  (boundedFlatCoefficientFullOpenBassEvaluationTargetTrack (P := P) a).cast
    (Category.assoc _ _ _) (Category.assoc _ _ _)

/-- The same two original chart movements flank that original target cylinder. -/
def boundedFlatCoefficientFullOpenBassEvaluationPastedDescTrack (a : Under R) :=
  ((Homotopy.precomp ((boundedFlatCoefficientFullOpenPrespectrumFunctor ι).map
    ((polynomialUnderCoefficient R).app a))
    (boundedFlatCoefficientSectionEvaluationHomotopy
      (i := (op P, (polynomialUnderFunctor R).obj a))
      (k := (op P, (laurentUnderFunctor R).obj a)) (𝟙 (op P), (underToLaurent R).app a))).trans
      (boundedFlatCoefficientFullOpenBassEvaluationTargetDescTrack (P := P) a)).trans
    (Homotopy.precomp ((boundedFlatCoefficientFullOpenPrespectrumFunctor ι).map
      ((polynomialUnderCoefficient R).app a))
      (boundedFlatCoefficientSectionEvaluationHomotopy
        (i := (op P, (polynomialUnderFunctor R).obj a))
        (k := (op P, (laurentUnderFunctor R).obj a)) (𝟙 (op P), (underToLaurentInvert R).app
          a))).symm

/-- The proved original boundary has the exact moving-descent association. -/
def boundedFlatCoefficientFullOpenBassEvaluationDescPasting (a : Under R) :
    (boundedFlatCoefficientFullOpenBassEvaluationSourceDescTrack ι a).RelHomotopy
      (boundedFlatCoefficientFullOpenBassEvaluationPastedDescTrack ι a) :=
  (boundedFlatCoefficientFullOpenBassEvaluationPasting ι a).ofLevels _ _ (fun _ => rfl)
    (by intro n; apply Homotopy.trans_level_congr
        · apply Homotopy.trans_level_congr <;> rfl
        · rfl)

private theorem pushoutDescTrack_level
    {A B C A' B' C' D : LoopPrespectrum.{v}}
    (f : A ⟶ B) (g : A ⟶ C) (f' : A' ⟶ B') (g' : A' ⟶ C')
    (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C')
    (Hf : Homotopy (f ≫ b) (a ≫ f')) (Hg : Homotopy (g ≫ c) (a ≫ g'))
    (p : B' ⟶ D) (q : C' ⟶ D) (K : Homotopy (f' ≫ p) (g' ≫ q)) (n : ℕ) :
    (((Hf.postcomp p).trans
      (((Homotopy.precomp a K).cast (Category.assoc _ _ _).symm
        (Category.assoc _ _ _).symm).trans (Hg.postcomp q).symm)).cast
          (Category.assoc _ _ _) (Category.assoc _ _ _)).level n =
    ((HomotopyPushout.mapSquareHomotopy f g f' g' a b c Hf Hg).postcomp
      (HomotopyPushout.desc f' g' p q K)).level n := by
  simp only [Homotopy.cast_level, HomotopyPushout.mapSquareHomotopy, Homotopy.postcomp_trans]
  apply Homotopy.trans_level_congr
  · rfl
  · apply Homotopy.trans_level_congr
    · rfl
    · exact congrArg (fun H => H.level n) (Homotopy.postcomp_symm Hg q).symm

private theorem nativeTargetDescTrack_level (a : Under R) (n : ℕ) :
    (boundedFlatCoefficientFullOpenBassEvaluationTargetDescTrack (P := P) a).level n =
    ((HomotopyPushout.mapSquareHomotopy
      ((boundedFlatCoefficientFullOpenPrespectrumFunctor ι).map ((polynomialUnderCoefficient
        R).app a))
      ((boundedFlatCoefficientFullOpenPrespectrumFunctor ι).map ((polynomialUnderCoefficient
        R).app a))
      (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
      (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
      (boundedFlatCoefficientSectionEvaluationPrespectrumMap (op P, a))
      (boundedFlatCoefficientSectionEvaluationPrespectrumMap (op P, (polynomialUnderFunctor R).obj
        a))
      (boundedFlatCoefficientSectionEvaluationPrespectrumMap (op P, (polynomialUnderFunctor R).obj
        a))
      (boundedFlatCoefficientSectionEvaluationHomotopy
        (i := (op P, a)) (k := (op P, (polynomialUnderFunctor R).obj a))
        (𝟙 (op P), (polynomialUnderCoefficient R).app a))
      (boundedFlatCoefficientSectionEvaluationHomotopy
        (i := (op P, a)) (k := (op P, (polynomialUnderFunctor R).obj a))
        (𝟙 (op P), (polynomialUnderCoefficient R).app a))).postcomp
          (boundedFlatCoefficientBassSquareComparison P a)).level n := by
  exact pushoutDescTrack_level
    ((boundedFlatCoefficientFullOpenPrespectrumFunctor ι).map ((polynomialUnderCoefficient R).app
      a))
    ((boundedFlatCoefficientFullOpenPrespectrumFunctor ι).map ((polynomialUnderCoefficient R).app
      a))
    (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
    (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
    (boundedFlatCoefficientSectionEvaluationPrespectrumMap (op P, a))
    (boundedFlatCoefficientSectionEvaluationPrespectrumMap (op P, (polynomialUnderFunctor R).obj a))
    (boundedFlatCoefficientSectionEvaluationPrespectrumMap (op P, (polynomialUnderFunctor R).obj a))
    (boundedFlatCoefficientSectionEvaluationHomotopy
      (i := (op P, a)) (k := (op P, (polynomialUnderFunctor R).obj a))
      (𝟙 (op P), (polynomialUnderCoefficient R).app a))
    (boundedFlatCoefficientSectionEvaluationHomotopy
      (i := (op P, a)) (k := (op P, (polynomialUnderFunctor R).obj a))
      (𝟙 (op P), (polynomialUnderCoefficient R).app a))
    (boundedFlatPerfectPrespectrumMap (laurentPlus P a))
    (boundedFlatPerfectPrespectrumMap (laurentMinus P a))
    (boundedFlatCoefficientBassSquareHomotopy P a) n

theorem CoefficientSectionEvaluationComposition.nativeSourceDesc_eq (a : Under R) :
    HomotopyPushout.desc
      ((boundedFlatCoefficientFullOpenPrespectrumFunctor ι).map ((polynomialUnderCoefficient
        R).app a))
      ((boundedFlatCoefficientFullOpenPrespectrumFunctor ι).map ((polynomialUnderCoefficient
        R).app a))
      ((boundedFlatCoefficientFullOpenPrespectrumFunctor ι).map ((underToLaurent R).app a) ≫
        boundedFlatCoefficientSectionEvaluationPrespectrumMap (op P, (laurentUnderFunctor R).obj a))
      ((boundedFlatCoefficientFullOpenPrespectrumFunctor ι).map ((underToLaurentInvert R).app a) ≫
        boundedFlatCoefficientSectionEvaluationPrespectrumMap (op P, (laurentUnderFunctor R).obj a))
      (boundedFlatCoefficientFullOpenBassEvaluationSourceDescTrack ι a) =
    StrictSquare.comparison (boundedFlatCoefficientFullOpenBassSquare ι a) ≫
      boundedFlatCoefficientSectionEvaluationPrespectrumMap (op P, (laurentUnderFunctor R).obj a)
        := by
  apply HomotopyPushout.hom_ext
  · rfl
  · rfl
  · intro n s x
    rfl

theorem CoefficientSectionEvaluationComposition.nativeTargetDesc_eq (a : Under R) :
    HomotopyPushout.desc
      ((boundedFlatCoefficientFullOpenPrespectrumFunctor ι).map ((polynomialUnderCoefficient
        R).app a))
      ((boundedFlatCoefficientFullOpenPrespectrumFunctor ι).map ((polynomialUnderCoefficient
        R).app a))
      (boundedFlatCoefficientSectionEvaluationPrespectrumMap (op P, (polynomialUnderFunctor R).obj
        a) ≫
        boundedFlatPerfectPrespectrumMap (laurentPlus P a))
      (boundedFlatCoefficientSectionEvaluationPrespectrumMap (op P, (polynomialUnderFunctor R).obj
        a) ≫
        boundedFlatPerfectPrespectrumMap (laurentMinus P a))
      (boundedFlatCoefficientFullOpenBassEvaluationTargetDescTrack (P := P) a) =
    boundedFlatCoefficientFullOpenBassSpanEvaluation ι a ≫
      boundedFlatCoefficientBassSquareComparison P a := by
  apply HomotopyPushout.hom_ext
  · rfl
  · rfl
  · intro n s x
    exact DFunLike.congr_fun (nativeTargetDescTrack_level ι a n) (s, x)

/-- Actual joint chart composition descends to both unchanged native comparison-map composites. -/
def boundedFlatCoefficientFullOpenBassComparisonEvaluationHomotopy (a : Under R) :
    Homotopy (StrictSquare.comparison (boundedFlatCoefficientFullOpenBassSquare ι a) ≫
      boundedFlatCoefficientSectionEvaluationPrespectrumMap (op P, (laurentUnderFunctor R).obj a))
    (boundedFlatCoefficientFullOpenBassSpanEvaluation ι a ≫
      boundedFlatCoefficientBassSquareComparison P a) :=
  (HomotopyPushout.descSquareHomotopy
    (H₀ := boundedFlatCoefficientFullOpenBassEvaluationSourceDescTrack ι a)
    (H₁ := boundedFlatCoefficientFullOpenBassEvaluationTargetDescTrack (P := P) a)
    ((boundedFlatCoefficientFullOpenPrespectrumFunctor ι).map ((polynomialUnderCoefficient R).app
      a))
    ((boundedFlatCoefficientFullOpenPrespectrumFunctor ι).map ((polynomialUnderCoefficient R).app
      a))
    (boundedFlatCoefficientSectionEvaluationHomotopy
      (i := (op P, (polynomialUnderFunctor R).obj a))
      (k := (op P, (laurentUnderFunctor R).obj a)) (𝟙 (op P), (underToLaurent R).app a))
    (boundedFlatCoefficientSectionEvaluationHomotopy
      (i := (op P, (polynomialUnderFunctor R).obj a))
      (k := (op P, (laurentUnderFunctor R).obj a)) (𝟙 (op P), (underToLaurentInvert R).app a))
    (boundedFlatCoefficientFullOpenBassEvaluationDescPasting ι a).toSquare).cast
      (nativeSourceDesc_eq ι a) (nativeTargetDesc_eq ι a)

/-- Positive endpoints retain the entire original chart evaluation track. -/
theorem boundedFlatCoefficientFullOpenBassComparisonEvaluationHomotopy_inl
    (a : Under R) (n : ℕ) (r : unitInterval)
    (x : ((boundedFlatCoefficientFullOpenPrespectrumFunctor ι).obj
      ((polynomialUnderFunctor R).obj a)).space n) :
    (boundedFlatCoefficientFullOpenBassComparisonEvaluationHomotopy ι a).level n
      (r, (HomotopyPushout.inl
        ((boundedFlatCoefficientFullOpenPrespectrumFunctor ι).map ((polynomialUnderCoefficient
          R).app a))
        ((boundedFlatCoefficientFullOpenPrespectrumFunctor ι).map ((polynomialUnderCoefficient
          R).app a))).map n x) =
    (boundedFlatCoefficientSectionEvaluationHomotopy
      (i := (op P, (polynomialUnderFunctor R).obj a))
      (k := (op P, (laurentUnderFunctor R).obj a)) (𝟙 (op P), (underToLaurent R).app a)).level n
        (r, x) := rfl

/-- The independent inverse-chart endpoint retains its own original evaluation track. -/
theorem boundedFlatCoefficientFullOpenBassComparisonEvaluationHomotopy_inr
    (a : Under R) (n : ℕ) (r : unitInterval)
    (x : ((boundedFlatCoefficientFullOpenPrespectrumFunctor ι).obj
      ((polynomialUnderFunctor R).obj a)).space n) :
    (boundedFlatCoefficientFullOpenBassComparisonEvaluationHomotopy ι a).level n
      (r, (HomotopyPushout.inr
        ((boundedFlatCoefficientFullOpenPrespectrumFunctor ι).map ((polynomialUnderCoefficient
          R).app a))
        ((boundedFlatCoefficientFullOpenPrespectrumFunctor ι).map ((polynomialUnderCoefficient
          R).app a))).map n x) =
    (boundedFlatCoefficientSectionEvaluationHomotopy
      (i := (op P, (polynomialUnderFunctor R).obj a))
      (k := (op P, (laurentUnderFunctor R).obj a)) (𝟙 (op P), (underToLaurentInvert R).app
        a)).level n (r, x) := rfl

/-- The original double cylinder retains independent comparison and chart-cylinder times. -/
theorem boundedFlatCoefficientFullOpenBassComparisonEvaluationHomotopy_cylinder
    (a : Under R) (n : ℕ) (r s : unitInterval)
    (x : ((boundedFlatCoefficientFullOpenPrespectrumFunctor ι).obj a).space n) :
    (boundedFlatCoefficientFullOpenBassComparisonEvaluationHomotopy ι a).level n
      (r, HomotopyPushout.cylinder
        ((boundedFlatCoefficientFullOpenPrespectrumFunctor ι).map ((polynomialUnderCoefficient
          R).app a))
        ((boundedFlatCoefficientFullOpenPrespectrumFunctor ι).map ((polynomialUnderCoefficient
          R).app a)) n (s, x)) =
      (boundedFlatCoefficientFullOpenBassEvaluationDescPasting ι a).toSquare.level n (r, (s, x))
        := rfl

end Quillen.PerfectComplexes
