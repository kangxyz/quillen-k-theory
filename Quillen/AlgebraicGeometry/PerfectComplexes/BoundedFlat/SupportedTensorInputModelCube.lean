/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedTensorInputNormalizedCube
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedTensorForgetSmallRectangle
public import Quillen.Waldhausen.SmallModel.IsoCube

/-! # The full genuine tensor input-forgetting cube in the original Models

The original common-universe functors lift the complete independently normalized cube. Both
actual tensor and geometric forgetting Model faces, and both original raw Model input squares,
remain in the conclusion.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open Quillen.Waldhausen
universe u
namespace Quillen.PerfectComplexes.SupportedTensorEvaluation
open GlobalSectionChangeIndex
variable {A B C D : Scheme.OpenPairs.{u}}
  (p : A ⟶ B) (q : C ⟶ D) (a : C ⟶ A) (b : D ⟶ B) (h : a ≫ p = q ≫ b)

/-- The actual tensor-first Model route with original support forgetting. -/
def modelInputForgetLeftRoute :=
  isoSquareRoute (tensorForgetModelIso p) (geometricForgetModelIso a)

/-- The actual input-first Model route with original support forgetting. -/
def modelInputForgetRightRoute :=
  isoSquareRoute (geometricForgetModelIso b) (tensorForgetModelIso q)

/-- The complete independent supported input cube agrees with its original ambient Model cube. -/
theorem tensorSupportedModelInputForgetCube :
    isoWhiskerRight (tensorSupportedRawModelInputIso p q a b h)
        (tensorCoefficientSupportedForgetModel C.obj.hom).functor ≪≫
        modelInputForgetRightRoute q b =
      modelInputForgetLeftRoute p a ≪≫
        isoWhiskerLeft (tensorCoefficientSupportedForgetModel B.obj.hom).functor
          (tensorUnitRawModelInputIso p.hom.right q.hom.right a.hom.right b.hom.right
            (congrArg (fun f : C ⟶ B => f.hom.right) h)) := by
  exact smallModelIsoCube
    (tensorSupportedRawNormalizedInputIso p q a b h)
    (tensorUnitRawNormalizedInputIso p.hom.right q.hom.right a.hom.right b.hom.right
      (congrArg (fun f : C ⟶ B => f.hom.right) h))
    (tensorForgetNormalizedIso p) (geometricForgetNormalizedIso a)
    (geometricForgetNormalizedIso b) (tensorForgetNormalizedIso q)
    (tensorSupportedNormalizedInputForgetCube p q a b h)

end Quillen.PerfectComplexes.SupportedTensorEvaluation
