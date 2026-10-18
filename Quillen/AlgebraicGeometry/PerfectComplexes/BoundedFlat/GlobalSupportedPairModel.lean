/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalSupportedPairReindex
public import Quillen.Aglib.CategoryTheory.ObjectProperty.LiftComposition

/-! # Exact original global supported reindex maps for actual open-pair squares -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.GlobalSectionChangeIndex
variable {A B : Scheme.OpenPairs.{u}} (g : A ⟶ B)

/-- The full evaluated reindexing iso is the original geometric pullback transition. -/
def supportedPairReindexEvaluationIso :
    supportedEvaluation (X := Opposite.op B.obj.right) B.obj.hom ⋙
        boundedFlatPerfectSupportedPullback g ≅
      supportedPairReindex g ⋙
        supportedEvaluation (X := Opposite.op A.obj.right) A.obj.hom :=
  Functor.fullyFaithfulCancelRight (boundedFlatPerfectSupported A.obj.hom).ι
    (Functor.isoWhiskerLeft (supported (X := Opposite.op B.obj.right) B.obj.hom).ι
      (Functor.isoWhiskerRight (evaluationPullbackIso g.hom.right)
        (boundedFlatPerfect A.obj.right).ι))

/-- The unchanged geometric exact pullback supplies exactness after original evaluation. -/
theorem supportedPairReindex_evaluation_exact :
    IsExact (supportedWaldhausen (X := Opposite.op B.obj.right) B.obj.hom).cof
      (supportedWaldhausen (X := Opposite.op B.obj.right) B.obj.hom).weq
      (boundedFlatPerfectSupportedWaldhausen A.obj.hom).cof
      (boundedFlatPerfectSupportedWaldhausen A.obj.hom).weq
      (supportedPairReindex g ⋙
        supportedEvaluation (X := Opposite.op A.obj.right) A.obj.hom) :=
  ExtensionCategory.isExact_of_natIso
    (supportedWaldhausen (X := Opposite.op B.obj.right) B.obj.hom)
    (boundedFlatPerfectSupportedWaldhausen A.obj.hom)
    ((supportedEvaluation_exact (X := Opposite.op B.obj.right) B.obj.hom).comp
      (boundedFlatPerfectSupportedPullback_exact g)) (supportedPairReindexEvaluationIso g)

/-- Reindexing is exact for the actual supported structures transported by evaluation. -/
theorem supportedPairReindex_exact :
    IsExact (supportedWaldhausen (X := Opposite.op B.obj.right) B.obj.hom).cof
      (supportedWaldhausen (X := Opposite.op B.obj.right) B.obj.hom).weq
      (supportedWaldhausen (X := Opposite.op A.obj.right) A.obj.hom).cof
      (supportedWaldhausen (X := Opposite.op A.obj.right) A.obj.hom).weq
      (supportedPairReindex g) := by
  let : (supportedEvaluation (X := Opposite.op A.obj.right) A.obj.hom).IsEquivalence :=
    supportedEvaluation_isEquivalence (X := Opposite.op A.obj.right) A.obj.hom
  exact {
  zero := fun hz => IsZero.of_full_of_faithful_of_isZero
    (supportedEvaluation (X := Opposite.op A.obj.right) A.obj.hom) _
    ((supportedPairReindex_evaluation_exact g).zero hz)
  cofibration := fun f hf => (supportedPairReindex_evaluation_exact g).cofibration f hf
  weak := fun f hf => (supportedPairReindex_evaluation_exact g).weak f hf
  pushout := fun hi hp => IsPushout.of_map_of_faithful
    (supportedEvaluation (X := Opposite.op A.obj.right) A.obj.hom)
    ((supportedPairReindex_evaluation_exact g).pushout hi hp) }

/-- The original supported section reindexing, with its literal original selected zero. -/
def supportedPairModelMap :
    supportedModel (X := Opposite.op B.obj.right) B.obj.hom ⟶
      supportedModel (X := Opposite.op A.obj.right) A.obj.hom where
  functor := supportedPairReindex g
  exact := supportedPairReindex_exact g
  zero := supportedPairReindex_zero g

/-- Forgetting support retains the original strict global Model square. -/
theorem supportedPairModelMap_forget :
    supportedPairModelMap g ≫ supportedForget (X := Opposite.op A.obj.right) A.obj.hom =
      supportedForget (X := Opposite.op B.obj.right) B.obj.hom ≫
        globalModel.map g.hom.right.op := by
  apply Model.Hom.ext
  exact supportedPairReindex_forget g

end Quillen.PerfectComplexes.GlobalSectionChangeIndex
