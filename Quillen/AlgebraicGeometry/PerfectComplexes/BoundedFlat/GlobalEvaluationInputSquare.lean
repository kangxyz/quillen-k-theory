/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalSupportedPairReindex
public import Quillen.Aglib.CategoryTheory.FiberedCategory.CocartesianEvaluationSquare

/-!
# Original global evaluation on a geometric pullback square

The ordinary pullback comparison is formed from the original geometric composition constraints.
Its evaluation square retains the actual section transitions and the strict global section
reindex equality. This input does not depend on tensor-unit comparison isomorphisms.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
open Quillen.CategoryTheory.GrothendieckSections Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.GlobalSectionChangeIndex

/-- The strict original section diagram retains geometric composition on underlying functors. -/
theorem globalReindex_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (globalModel.map (f ≫ g).op).functor =
      (globalModel.map g.op).functor ⋙ (globalModel.map f.op).functor :=
  congrArg Quillen.Waldhausen.IteratedS.Model.Hom.functor (globalModel.map_comp g.op f.op)

/-- The two original evaluation transitions, with all source and target associations retained. -/
def evaluationPullbackRouteIso {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    globalEvaluation (Opposite.op Z) ⋙
        (boundedFlatPerfectPullback g ⋙ boundedFlatPerfectPullback f) ≅
      ((globalModel.map g.op).functor ⋙ (globalModel.map f.op).functor) ⋙
        globalEvaluation (Opposite.op X) :=
  (originalCoefficientRouteIso boundedFlatPerfectPseudofunctor g.op f.op).symm

/-- The geometric evaluation comparison is the inverse original coefficient comparison. -/
theorem evaluationPullbackIso_original {X Y : Scheme.{u}} (f : X ⟶ Y) :
    evaluationPullbackIso f =
      (originalCoefficientIso boundedFlatPerfectPseudofunctor f.op).symm := rfl

/-- The route uses the actual evaluation transitions, not a comparison reconstructed from tensor.
-/
theorem evaluationPullbackRouteIso_hom {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (evaluationPullbackRouteIso f g).hom =
      (Functor.associator (globalEvaluation (Opposite.op Z))
        (boundedFlatPerfectPullback g) (boundedFlatPerfectPullback f)).inv ≫
      whiskerRight (evaluationPullbackIso g).hom (boundedFlatPerfectPullback f) ≫
      (Functor.associator (globalModel.map g.op).functor
        (globalEvaluation (Opposite.op Y)) (boundedFlatPerfectPullback f)).hom ≫
      whiskerLeft (globalModel.map g.op).functor (evaluationPullbackIso f).hom ≫
      (Functor.associator (globalModel.map g.op).functor (globalModel.map f.op).functor
        (globalEvaluation (Opposite.op X))).inv := by
  simp only [evaluationPullbackRouteIso, originalCoefficientRouteIso,
    evaluationPullbackIso_original, Iso.symm_hom, Iso.trans_inv, Iso.symm_inv,
    isoWhiskerRight_inv, isoWhiskerLeft_inv, Category.assoc]
  rfl

/-- Original evaluation respects the actual geometric composition comparison and strict reindex.
-/
theorem evaluationPullbackIso_comp_hom {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    whiskerLeft (globalEvaluation (Opposite.op Z))
        (boundedFlatPerfectPullbackCompIso f g).hom ≫
        (evaluationPullbackRouteIso f g).hom =
      (evaluationPullbackIso (f ≫ g)).hom ≫
        eqToHom (congrArg (fun F => F ⋙ globalEvaluation (Opposite.op X))
          (globalReindex_comp f g)) := by
  have hc : (evaluationPullbackIso (f ≫ g)).inv ≫
      whiskerLeft (globalEvaluation (Opposite.op Z))
        (boundedFlatPerfectPullbackCompIso f g).hom =
      eqToHom (congrArg (fun F => F ⋙ globalEvaluation (Opposite.op X))
        (globalReindex_comp f g)) ≫ (evaluationPullbackRouteIso f g).inv := by
    exact originalCoefficientIso_comp_hom boundedFlatPerfectPseudofunctor g.op f.op
  apply (cancel_epi (evaluationPullbackIso (f ≫ g)).inv).mp
  rw [← Category.assoc, hc]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.inv_hom_id_assoc]

/-- Equality of geometric arrows transports both original evaluation routes. -/
theorem evaluationPullbackIso_congr_hom {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) :
    whiskerLeft (globalEvaluation (Opposite.op Y))
        (eqToIso (congrArg boundedFlatPerfectPullback h)).hom ≫
        (evaluationPullbackIso g).hom =
      (evaluationPullbackIso f).hom ≫
        eqToHom (congrArg (fun k : X ⟶ Y =>
          (globalModel.map k.op).functor ⋙ globalEvaluation (Opposite.op X)) h) := by
  subst g
  simp

variable {A B C D : Scheme.{u}}
  (p : A ⟶ B) (q : C ⟶ D) (a : C ⟶ A) (b : D ⟶ B) (h : a ≫ p = q ≫ b)

/-- The original ordinary geometric input comparison around an actual scheme square. -/
def pullbackInputSquareIso :
    boundedFlatPerfectPullback p ⋙ boundedFlatPerfectPullback a ≅
      boundedFlatPerfectPullback b ⋙ boundedFlatPerfectPullback q :=
  (boundedFlatPerfectPullbackCompIso a p).symm ≪≫
    eqToIso (congrArg boundedFlatPerfectPullback h) ≪≫
    boundedFlatPerfectPullbackCompIso q b

include h in
/-- Original global section reindexing commutes strictly on the actual geometric square. -/
theorem globalReindexInputSquare :
    (globalModel.map p.op).functor ⋙ (globalModel.map a.op).functor =
      (globalModel.map b.op).functor ⋙ (globalModel.map q.op).functor :=
  (globalReindex_comp a p).symm.trans
    ((congrArg (fun f : C ⟶ B => (globalModel.map f.op).functor) h).trans (globalReindex_comp q b))

/-- The complete two-route evaluation square retains the raw geometric comparison. -/
theorem evaluationPullbackInputSquare_hom :
    whiskerLeft (globalEvaluation (Opposite.op B))
        (pullbackInputSquareIso p q a b h).hom ≫
        (evaluationPullbackRouteIso q b).hom =
      (evaluationPullbackRouteIso a p).hom ≫
        eqToHom (congrArg (fun F => F ⋙ globalEvaluation (Opposite.op C))
          (globalReindexInputSquare p q a b h)) := by
  exact originalCoefficientInputSquare_hom boundedFlatPerfectPseudofunctor
    p.op a.op b.op q.op (congrArg (fun f : C ⟶ B => f.op) h)

end Quillen.PerfectComplexes.GlobalSectionChangeIndex
