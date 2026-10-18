/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalSupportedModels
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.PairPullback

/-! # Original global section reindexing on genuine open-pair squares -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.Complex
open Quillen.CategoryTheory.GrothendieckSections
universe u
namespace Quillen.PerfectComplexes.GlobalSectionChangeIndex

/-- The original section transition identifies geometric pullback with reindexed evaluation. -/
def evaluationPullbackIso {X Y : Scheme.{u}} (g : X ⟶ Y) :
    globalEvaluation (Opposite.op Y) ⋙ boundedFlatPerfectPullback g ≅
      (globalModel.map g.op).functor ⋙ globalEvaluation (Opposite.op X) :=
  originalEvaluationTransitionIso boundedFlatPerfectPseudofunctor (Opposite.op Y)
      (Under.mk g.op) ≪≫
    eqToIso (originalEvaluation_reindex boundedFlatPerfectPseudofunctor
      (Opposite.op Y) g.op).symm

/-- Every actual open-pair square preserves the evaluated support of original sections. -/
theorem pairReindex_supported {A B : Scheme.OpenPairs.{u}} (g : A ⟶ B)
    (S : globalModel.obj (Opposite.op B.obj.right))
    (hS : supported (X := Opposite.op B.obj.right) B.obj.hom S) :
    supported (X := Opposite.op A.obj.right) A.obj.hom
      ((globalModel.map g.hom.right.op).functor.obj S) := by
  have hp := boundedFlatPerfectSupported_pairPullback g
    (K := ((globalEvaluation (Opposite.op B.obj.right)).obj S).obj)
    ⟨((globalEvaluation (Opposite.op B.obj.right)).obj S).property, hS⟩
  let e := (restrict A.obj.hom).mapIso
    ((boundedFlatPerfect A.obj.right).ι.mapIso ((evaluationPullbackIso g.hom.right).app S))
  intro n
  exact (hp.2 n).of_iso e

/-- Reindex the actual supported global sections without changing their underlying functor. -/
def supportedPairReindex {A B : Scheme.OpenPairs.{u}} (g : A ⟶ B) :
    (supported (X := Opposite.op B.obj.right) B.obj.hom).FullSubcategory ⥤
      (supported (X := Opposite.op A.obj.right) A.obj.hom).FullSubcategory :=
  (supported (X := Opposite.op A.obj.right) A.obj.hom).lift
    ((supported (X := Opposite.op B.obj.right) B.obj.hom).ι ⋙
      (globalModel.map g.hom.right.op).functor)
    (fun S => pairReindex_supported g S.obj S.property)

/-- The entire forgetful square is literal equality. -/
theorem supportedPairReindex_forget {A B : Scheme.OpenPairs.{u}} (g : A ⟶ B) :
    supportedPairReindex g ⋙
        (supported (X := Opposite.op A.obj.right) A.obj.hom).ι =
      (supported (X := Opposite.op B.obj.right) B.obj.hom).ι ⋙
        (globalModel.map g.hom.right.op).functor := rfl

/-- Reindexing retains the original selected section zero. -/
theorem supportedPairReindex_zero {A B : Scheme.OpenPairs.{u}} (g : A ⟶ B) :
    (supportedPairReindex g).obj
        (supportedZero (X := Opposite.op B.obj.right) B.obj.hom) =
      supportedZero (X := Opposite.op A.obj.right) A.obj.hom := by
  apply ObjectProperty.FullSubcategory.ext
  exact (globalModel.map g.hom.right.op).zero

end Quillen.PerfectComplexes.GlobalSectionChangeIndex
