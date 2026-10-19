/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationNormalization
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.NormalizedPullbackCoherence
public import Quillen.Aglib.CategoryTheory.Functor.IsoSquareConjugateComposition
public import Quillen.Waldhausen.SConstruction.Iterated.PrespectrumPastingHomotopy

/-!
# Composition of the original normalized global evaluation

The actual geometric composition constraint and the unchanged evaluation comparisons form
an exact Model pasting. Both raw pullback and evaluation chosen-zero normalizations are
retained. Realization gives the two-parameter comparison of these Model routes; identification
with the original split geometric spectrum track is a separate step.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS
open Quillen.CategoryTheory.GrothendieckSections
universe u
namespace Quillen.PerfectComplexes.GlobalSectionChangeIndex

/-- The original normalized geometric composition in the actual small Model fibers. -/
def evaluationRawCompIso {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (evaluationRawMap (f ≫ g)).functor ≅
      (evaluationRawMap g).functor ⋙ (evaluationRawMap f).functor :=
  isoWhiskerLeft AsSmall.down
    (isoWhiskerRight (boundedFlatNormalizedPullbackCompIso f g) AsSmall.up)

/-- The coefficient comparison uses exactly the original raw normalization and composition. -/
theorem evaluationRawCompIso_smallCoefficient {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    evaluationRawCompIso f g =
      smallCoefficientCompIso boundedFlatPerfectPseudofunctor g.op f.op
        (evaluationRawNormalization g) (evaluationRawNormalization f)
        (evaluationRawNormalization (f ≫ g)) := rfl

/-- The original target composition, evaluated after the unchanged normalized evaluation. -/
def evaluationCompositionTargetIso {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (evaluationModel (op Z) ≫ evaluationRawMap (f ≫ g)).functor ≅
      ((evaluationModel (op Z) ≫ evaluationRawMap g) ≫ evaluationRawMap f).functor :=
  isoWhiskerLeft (evaluationModel (op Z)).functor (evaluationRawCompIso f g) ≪≫
    (Functor.associator (evaluationModel (op Z)).functor
      (evaluationRawMap g).functor (evaluationRawMap f).functor).symm

/-- Strict global reindexing followed by the original second evaluation comparison. -/
def evaluationCompositionFirstIso {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (globalModel.map (f ≫ g).op ≫ evaluationModel (op X)).functor ≅
      ((globalModel.map g.op ≫ evaluationModel (op Y)) ≫ evaluationRawMap f).functor :=
  eqToIso (congrArg (fun S => S ⋙ (evaluationModel (op X)).functor)
      (globalReindex_comp f g)) ≪≫
    Functor.associator (globalModel.map g.op).functor (globalModel.map f.op).functor
      (evaluationModel (op X)).functor ≪≫
    isoWhiskerLeft (globalModel.map g.op).functor (evaluationComparisonIso f) ≪≫
    (Functor.associator (globalModel.map g.op).functor (evaluationModel (op Y)).functor
      (evaluationRawMap f).functor).symm

/-- The original first evaluation comparison postcomposed by actual raw pullback. -/
def evaluationCompositionSecondIso {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ((globalModel.map g.op ≫ evaluationModel (op Y)) ≫ evaluationRawMap f).functor ≅
      ((evaluationModel (op Z) ≫ evaluationRawMap g) ≫ evaluationRawMap f).functor :=
  isoWhiskerRight (evaluationComparisonIso g) (evaluationRawMap f).functor

/-- The original raw Model arrow keeps exactly the original normalized small functor. -/
theorem evaluationRawMap_functor {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (evaluationRawMap f).functor = smallModelFunctor (boundedFlatNormalizedPullback f) := rfl

/-- The actual strict global Model arrow uses the unchanged cocartesian reindex functor. -/
theorem evaluationReindexFunctor_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (globalModel.map f.op).functor =
      Quillen.CategoryTheory.StrictSections.underCocartesianReindex
        (Pseudofunctor.Grothendieck.forget boundedFlatPerfectPseudofunctor) f.op := rfl

private theorem liftedComparison_comp_app
    {C : Type*} [Category C]
    (F : Pseudofunctor (LocallyDiscrete C) Cat)
    {a b c : C} (f : a ⟶ b) (g : b ⟶ c)
    {Nf : F.obj ⟨a⟩ ⥤ F.obj ⟨b⟩} {Ng : F.obj ⟨b⟩ ⥤ F.obj ⟨c⟩}
    {Nfg : F.obj ⟨a⟩ ⥤ F.obj ⟨c⟩}
    (nf : (F.map f.toLoc).toFunctor ≅ Nf) (ng : (F.map g.toLoc).toFunctor ≅ Ng)
    (nfg : (F.map (f ≫ g).toLoc).toFunctor ≅ Nfg)
    (x : Quillen.CategoryTheory.StrictSections.underCocartesian
      (Pseudofunctor.Grothendieck.forget F) a) :
    (smallCoefficientIso F (f ≫ g) nfg).hom.app x ≫
      (smallCoefficientCompIso F f g nf ng nfg).hom.app
        ((originalEvaluation F a ⋙ AsSmall.up).obj x) =
    (eqToHom (congrArg (fun S => S ⋙ (originalEvaluation F c ⋙ AsSmall.up))
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

attribute [local irreducible] evaluationComparisonIso evaluationRawCompIso
  evaluationNormalizationIso evaluationRawNormalization
  smallCoefficientIso smallCoefficientCompIso isoSquareConjugate

private theorem normalizedCoefficient_comp_app
    {C : Type*} [Category C]
    (F : Pseudofunctor (LocallyDiscrete C) Cat)
    {a b c : C} (f : a ⟶ b) (g : b ⟶ c)
    {Nf : F.obj ⟨a⟩ ⥤ F.obj ⟨b⟩} {Ng : F.obj ⟨b⟩ ⥤ F.obj ⟨c⟩}
    {Nfg : F.obj ⟨a⟩ ⥤ F.obj ⟨c⟩}
    (nf : (F.map f.toLoc).toFunctor ≅ Nf) (ng : (F.map g.toLoc).toFunctor ≅ Ng)
    (nfg : (F.map (f ≫ g).toLoc).toFunctor ≅ Nfg)
    {E₀ : Quillen.CategoryTheory.StrictSections.underCocartesian
      (Pseudofunctor.Grothendieck.forget F) a ⥤ Quillen.Waldhausen.SmallModel (F.obj ⟨a⟩)}
    {E₁ : Quillen.CategoryTheory.StrictSections.underCocartesian
      (Pseudofunctor.Grothendieck.forget F) b ⥤ Quillen.Waldhausen.SmallModel (F.obj ⟨b⟩)}
    {E₂ : Quillen.CategoryTheory.StrictSections.underCocartesian
      (Pseudofunctor.Grothendieck.forget F) c ⥤ Quillen.Waldhausen.SmallModel (F.obj ⟨c⟩)}
    (z₀ : originalEvaluation F a ⋙ AsSmall.up ≅ E₀)
    (z₁ : originalEvaluation F b ⋙ AsSmall.up ≅ E₁)
    (z₂ : originalEvaluation F c ⋙ AsSmall.up ≅ E₂)
    (x : Quillen.CategoryTheory.StrictSections.underCocartesian
      (Pseudofunctor.Grothendieck.forget F) a) :
    (isoSquareConjugate (smallCoefficientIso F (f ≫ g) nfg) z₀ z₂).hom.app x ≫
        (smallCoefficientCompIso F f g nf ng nfg).hom.app (E₀.obj x) =
      (eqToHom (congrArg (fun S => S ⋙ E₂)
        (Quillen.CategoryTheory.StrictSections.underCocartesianReindex_comp
          (Pseudofunctor.Grothendieck.forget F) f g))).app x ≫
        (isoSquareConjugate (smallCoefficientIso F g ng) z₁ z₂).hom.app
          ((Quillen.CategoryTheory.StrictSections.underCocartesianReindex
            (Pseudofunctor.Grothendieck.forget F) f).obj x) ≫
        (smallModelFunctor Ng).map
          ((isoSquareConjugate (smallCoefficientIso F f nf) z₀ z₁).hom.app x) :=
  isoSquareConjugate_comp_app
    (Quillen.CategoryTheory.StrictSections.underCocartesianReindex
      (Pseudofunctor.Grothendieck.forget F) f)
    (Quillen.CategoryTheory.StrictSections.underCocartesianReindex
      (Pseudofunctor.Grothendieck.forget F) g)
    (Quillen.CategoryTheory.StrictSections.underCocartesianReindex
      (Pseudofunctor.Grothendieck.forget F) (f ≫ g))
    (Quillen.CategoryTheory.StrictSections.underCocartesianReindex_comp
      (Pseudofunctor.Grothendieck.forget F) f g)
    (smallModelFunctor Nf) (smallModelFunctor Ng) (smallModelFunctor Nfg)
    (smallCoefficientIso F f nf) (smallCoefficientIso F g ng)
    (smallCoefficientIso F (f ≫ g) nfg) (smallCoefficientCompIso F f g nf ng nfg)
    z₀ z₁ z₂ (liftedComparison_comp_app F f g nf ng nfg) x

private theorem normalizedComparison_comp_app {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (x : globalModel.obj (op Z)) :
    (isoSquareConjugate
      (smallCoefficientIso boundedFlatPerfectPseudofunctor (f ≫ g).op
        (evaluationRawNormalization (f ≫ g)))
      (evaluationNormalizationIso (op Z)) (evaluationNormalizationIso (op X))).hom.app x ≫
        (smallCoefficientCompIso boundedFlatPerfectPseudofunctor g.op f.op
          (evaluationRawNormalization g) (evaluationRawNormalization f)
          (evaluationRawNormalization (f ≫ g))).hom.app ((evaluationModel (op Z)).functor.obj x) =
      (eqToHom (congrArg (fun S => S ⋙ (evaluationModel (op X)).functor)
        (globalReindex_comp f g))).app x ≫
        (isoSquareConjugate
          (smallCoefficientIso boundedFlatPerfectPseudofunctor f.op (evaluationRawNormalization f))
          (evaluationNormalizationIso (op Y)) (evaluationNormalizationIso (op X))).hom.app
            ((globalModel.map g.op).functor.obj x) ≫
        (evaluationRawMap f).functor.map ((isoSquareConjugate
          (smallCoefficientIso boundedFlatPerfectPseudofunctor g.op (evaluationRawNormalization g))
          (evaluationNormalizationIso (op Z)) (evaluationNormalizationIso (op Y))).hom.app x) := by
  simp only [evaluationRawMap_functor, evaluationReindexFunctor_eq]
  exact normalizedCoefficient_comp_app boundedFlatPerfectPseudofunctor g.op f.op
    (evaluationRawNormalization g) (evaluationRawNormalization f)
    (evaluationRawNormalization (f ≫ g))
    (evaluationNormalizationIso (op Z)) (evaluationNormalizationIso (op Y))
    (evaluationNormalizationIso (op X)) x

/-- Composition retains all three original evaluation normalizations on every component. -/
theorem evaluationComparisonIso_comp_app {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (x : globalModel.obj (op Z)) :
    (evaluationComparisonIso (f ≫ g)).hom.app x ≫
        (evaluationRawCompIso f g).hom.app ((evaluationModel (op Z)).functor.obj x) =
      (eqToHom (congrArg (fun S => S ⋙ (evaluationModel (op X)).functor)
        (globalReindex_comp f g))).app x ≫
        (evaluationComparisonIso f).hom.app ((globalModel.map g.op).functor.obj x) ≫
        (evaluationRawMap f).functor.map ((evaluationComparisonIso g).hom.app x) := by
  rw [evaluationComparisonIso_smallCoefficient, evaluationRawCompIso_smallCoefficient,
    evaluationComparisonIso_smallCoefficient, evaluationComparisonIso_smallCoefficient]
  exact normalizedComparison_comp_app f g x

private theorem comparison_pasting_hom
    {A B C D E F : Type*} [Category A] [Category B] [Category C]
    [Category D] [Category E] [Category F]
    (Sf : A ⥤ B) (Sg : B ⥤ C) (Sfg : A ⥤ C) (hS : Sfg = Sf ⋙ Sg)
    (U₀ : A ⥤ D) (U₁ : B ⥤ E) (U₂ : C ⥤ F)
    (Pf : D ⥤ E) (Pg : E ⥤ F) (Pfg : D ⥤ F)
    (κf : Sf ⋙ U₁ ≅ U₀ ⋙ Pf) (κg : Sg ⋙ U₂ ≅ U₁ ⋙ Pg)
    (κfg : Sfg ⋙ U₂ ≅ U₀ ⋙ Pfg) (β : Pfg ≅ Pf ⋙ Pg)
    (h : ∀ x, κfg.hom.app x ≫ β.hom.app (U₀.obj x) =
      (eqToHom (congrArg (fun S => S ⋙ U₂) hS)).app x ≫
        κg.hom.app (Sf.obj x) ≫ Pg.map (κf.hom.app x)) :
    κfg.hom ≫ (isoWhiskerLeft U₀ β ≪≫ (Functor.associator U₀ Pf Pg).symm).hom =
      (eqToIso (congrArg (fun S => S ⋙ U₂) hS) ≪≫ Functor.associator Sf Sg U₂ ≪≫
        isoWhiskerLeft Sf κg ≪≫ (Functor.associator Sf U₁ Pg).symm).hom ≫
        (isoWhiskerRight κf Pg).hom := by
  apply NatTrans.ext
  funext x
  simpa only [Iso.trans_hom, Iso.symm_hom, isoWhiskerLeft_hom,
    isoWhiskerRight_hom, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, eqToIso.hom,
    Category.id_comp, Category.comp_id, Category.assoc] using h x

/-- The exact two original Model transformation pastings agree. -/
theorem evaluationComposition_pasting {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (evaluationComparisonIso (f ≫ g)).hom ≫ (evaluationCompositionTargetIso f g).hom =
      (evaluationCompositionFirstIso f g).hom ≫ (evaluationCompositionSecondIso f g).hom :=
  comparison_pasting_hom
    (globalModel.map g.op).functor (globalModel.map f.op).functor
    (globalModel.map (f ≫ g).op).functor (globalReindex_comp f g)
    (evaluationModel (op Z)).functor (evaluationModel (op Y)).functor
    (evaluationModel (op X)).functor (evaluationRawMap g).functor
    (evaluationRawMap f).functor (evaluationRawMap (f ≫ g)).functor
    (evaluationComparisonIso g) (evaluationComparisonIso f)
    (evaluationComparisonIso (f ≫ g)) (evaluationRawCompIso f g)
    (evaluationComparisonIso_comp_app f g)

/-- Realization retains the complete original two-route Model comparison. -/
def evaluationModelCompositionRelHomotopy {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :=
  prespectrumPastingHomotopy
    (V := globalModel.obj (op Z)) (W := modelOf (boundedFlatPerfectWaldhausen X))
    (F := globalModel.map (f ≫ g).op ≫ evaluationModel (op X))
    (G := evaluationModel (op Z) ≫ evaluationRawMap (f ≫ g))
    (G' := (globalModel.map g.op ≫ evaluationModel (op Y)) ≫ evaluationRawMap f)
    (H := (evaluationModel (op Z) ≫ evaluationRawMap g) ≫ evaluationRawMap f)
    (evaluationComparisonIso (f ≫ g)).hom (evaluationCompositionTargetIso f g).hom
    (evaluationCompositionFirstIso f g).hom (evaluationCompositionSecondIso f g).hom
    (fun _ => (boundedFlatPerfectWaldhausen X).smallModel.weq_iso _ inferInstance)
    (fun _ => (boundedFlatPerfectWaldhausen X).smallModel.weq_iso _ inferInstance)
    (fun _ => (boundedFlatPerfectWaldhausen X).smallModel.weq_iso _ inferInstance)
    (fun _ => (boundedFlatPerfectWaldhausen X).smallModel.weq_iso _ inferInstance)
    (evaluationComposition_pasting f g)

end Quillen.PerfectComplexes.GlobalSectionChangeIndex
