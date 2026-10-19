/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitRawInputSquare
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalEvaluationNaturality

/-! # The original tensor input square with its actual Model zero normalizations

The raw square is constructed first. Both routes are then conjugated by the existing genuine
tensor and geometric pullback normalizations, before the original common-universe lift.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes
open GlobalSectionChangeIndex
variable {A B C D : Scheme.{u}}
  (p : A ⟶ B) (q : C ⟶ D) (a : C ⟶ A) (b : D ⟶ B) (h : a ≫ p = q ≫ b)

/-- Conjugate the independently specified raw square by its four original zero normalizations. -/
def tensorUnitRawNormalizedInputIso :=
  isoWhiskerRight (tensorUnitPullbackNormalization p).symm
      _ ≪≫
    isoWhiskerLeft (boundedFlatPerfectTensorUnitPullback p)
      (evaluationRawNormalization a).symm ≪≫
    tensorUnitRawInputIso p q a b h ≪≫
    isoWhiskerLeft (boundedFlatPerfectPullback b) (tensorUnitPullbackNormalization q) ≪≫
    isoWhiskerRight (evaluationRawNormalization b)
      _

/-- The actual based Model functors retain that same raw square through the common-universe lift.
-/
def tensorUnitRawModelInputIso :
    (tensorUnitPullbackModelMap p ≫ evaluationRawMap a).functor ≅
      (evaluationRawMap b ≫ tensorUnitPullbackModelMap q).functor :=
  isoWhiskerRight (isoWhiskerLeft AsSmall.down
    (tensorUnitRawNormalizedInputIso p q a b h)) AsSmall.up

end Quillen.PerfectComplexes
