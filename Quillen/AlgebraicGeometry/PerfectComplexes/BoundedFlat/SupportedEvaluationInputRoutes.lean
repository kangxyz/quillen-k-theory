/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalSupportedPairDiagram
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalEvaluationInputSquare
public import Quillen.Aglib.CategoryTheory.Functor.IsoRouteConjugation
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedEvaluationInputComponents

/-! # Original supported input routes and their genuine forgetful image

The actual supported geometric transitions form a complete two-route square. Its proof
uses the faithful inclusion only on morphisms of the original supported category, with
all actual geometric composition and section reindex transports retained.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.GlobalSectionChangeIndex
attribute [local irreducible] globalModel globalEvaluation
  evaluationPullbackIso supportedPairReindexEvaluationIso

/-- The actual supported section functor retains strict composition on every pair. -/
theorem supportedReindex_comp {A B C : Scheme.OpenPairs.{u}} (f : A ⟶ B) (g : B ⟶ C) :
    (supportedPairModelMap (f ≫ g)).functor =
      (supportedPairModelMap g).functor ⋙ (supportedPairModelMap f).functor :=
  congrArg Model.Hom.functor (pairSupported.map_comp g.op f.op)

/-- Both original supported evaluation transitions, including all categorical associations. -/
def supportedEvaluationRouteIso {A B C : Scheme.OpenPairs.{u}} (f : A ⟶ B) (g : B ⟶ C) :=
  (isoSquareRoute (supportedPairReindexEvaluationIso g).symm
    (supportedPairReindexEvaluationIso f).symm).symm

variable {A B C D : Scheme.OpenPairs.{u}}
  (p : A ⟶ B) (q : C ⟶ D) (a : C ⟶ A) (b : D ⟶ B) (h : a ≫ p = q ≫ b)

include h in
/-- The original supported section reindex square, as a full functor equality. -/
theorem supportedReindexInputSquare :
    (supportedPairModelMap p).functor ⋙ (supportedPairModelMap a).functor =
      (supportedPairModelMap b).functor ⋙ (supportedPairModelMap q).functor :=
  (supportedReindex_comp a p).symm.trans
    ((congrArg (fun f : C ⟶ B => (supportedPairModelMap f).functor) h).trans
      (supportedReindex_comp q b))

/-- The raw geometric comparison remains wholly inside the original supported categories. -/
def supportedPullbackInputSquareIso :
    boundedFlatPerfectSupportedPullback p ⋙ boundedFlatPerfectSupportedPullback a ≅
      boundedFlatPerfectSupportedPullback b ⋙ boundedFlatPerfectSupportedPullback q :=
  (boundedFlatPerfectSupportedPullbackCompIso a p).symm ≪≫
    eqToIso (congrArg boundedFlatPerfectSupportedPullback h) ≪≫
    boundedFlatPerfectSupportedPullbackCompIso q b

/-- Both complete supported evaluation transitions retain their original ambient components. -/
theorem supportedEvaluationRoute_forget_hom_app {E F G : Scheme.OpenPairs.{u}}
    (f : E ⟶ F) (g : F ⟶ G)
    (K : (supported (X := op G.obj.right) G.obj.hom).FullSubcategory) :
    (tensorCoefficientSupportedForget E.obj.hom).map
        ((supportedEvaluationRouteIso f g).hom.app K) =
      (evaluationPullbackRouteIso f.hom.right g.hom.right).hom.app K.obj := by
  simp only [supportedEvaluationRouteIso, evaluationPullbackRouteIso_hom, isoSquareRoute,
    Iso.symm_hom, Iso.trans_inv, Iso.symm_inv, isoWhiskerLeft_inv, isoWhiskerRight_inv,
    NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.map_comp, Category.id_comp, Category.comp_id,
    boundedFlatPerfectSupportedPullback_forget_map]
  rw [supportedReindexEvaluation_forget_hom_app,
    supportedPairReindexEvaluationIso_forget_hom_app]

end Quillen.PerfectComplexes.GlobalSectionChangeIndex
