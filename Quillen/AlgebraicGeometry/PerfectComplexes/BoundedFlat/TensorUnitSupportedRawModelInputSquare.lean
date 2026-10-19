/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitSupportedRawInputSquare
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedEvaluationModelNaturality

/-! # The actual supported raw tensor input square through its original rebases

All four raw geometric and tensor zero normalizations are retained before the original
common-universe lift. The square is constructed independently of evaluation or its inverse.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes
open SupportedTensorEvaluation
variable {A B C D : Scheme.OpenPairs.{u}}
  (p : A ⟶ B) (q : C ⟶ D) (a : C ⟶ A) (b : D ⟶ B) (h : a ≫ p = q ≫ b)

/-- The four original chosen-zero isomorphisms surround the independent supported raw square. -/
def tensorSupportedRawNormalizedInputIso :=
  isoWhiskerRight (tensorSupportedPairNormalization p).symm _ ≪≫
    isoWhiskerLeft (tensorSupportedPairFunctor p) (evaluationRawNormalization a).symm ≪≫
    tensorSupportedRawInputIso p q a b h ≪≫
    isoWhiskerLeft (boundedFlatPerfectSupportedPullback b) (tensorSupportedPairNormalization q) ≪≫
    isoWhiskerRight (evaluationRawNormalization b) _

/-- The actual supported Model input square preserves all raw normalization paths. -/
def tensorSupportedRawModelInputIso :
    (tensorSupportedPairModelMap p ≫ evaluationRawMap a).functor ≅
      (evaluationRawMap b ≫ tensorSupportedPairModelMap q).functor :=
  isoWhiskerRight (isoWhiskerLeft AsSmall.down
    (tensorSupportedRawNormalizedInputIso p q a b h)) AsSmall.up

end Quillen.PerfectComplexes
