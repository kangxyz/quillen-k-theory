/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitRawModelInputSquare
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalEvaluationInputSquare
public import Quillen.Waldhausen.SmallModel.CoefficientInputSquare
public import Quillen.Aglib.CategoryTheory.Functor.IsoSquareReplacement
public import
  Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.PseudofunctorComponents

/-! # The genuine raw tensor square in the original normalized coefficient square

The raw tensor square is defined independently from actual tensor unitors and geometric
pullback composition. This identifies its four original zero normalizations with the
normalized coefficient square, retaining both evaluation routes for later Model transport.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
open Quillen.CategoryTheory.GrothendieckSections Quillen.Waldhausen
universe u
namespace Quillen.PerfectComplexes
open GlobalSectionChangeIndex

/-- The actual tensor unitor followed by its original chosen-zero normalization. -/
def tensorCoefficientNormalization {A B : Scheme.{u}} (p : A ⟶ B) :=
  (boundedFlatPerfectTensorUnitPullbackIso p).symm ≪≫ tensorUnitPullbackNormalization p

variable {A B C D : Scheme.{u}}
  (p : A ⟶ B) (q : C ⟶ D) (a : C ⟶ A) (b : D ⟶ B) (h : a ≫ p = q ≫ b)

/-- The independently defined raw tensor square uses exactly the four original normalizations. -/
theorem tensorUnitRawNormalizedInputIso_eq :
    tensorUnitRawNormalizedInputIso p q a b h =
      normalizedCoefficientInputSquareIso boundedFlatPerfectPseudofunctor
        p.op a.op b.op q.op (congrArg (fun f : C ⟶ B => f.op) h)
        (tensorCoefficientNormalization p) (evaluationRawNormalization a)
        (evaluationRawNormalization b) (tensorCoefficientNormalization q) := by
  have hs := isoSquareReplacement_normalization
    (boundedFlatPerfectTensorUnitPullbackIso p) (boundedFlatPerfectTensorUnitPullbackIso q)
    (tensorUnitPullbackNormalization p) (evaluationRawNormalization a)
    (evaluationRawNormalization b) (tensorUnitPullbackNormalization q)
    (pullbackInputSquareIso p q a b h)
  simpa only [tensorUnitRawNormalizedInputIso, tensorUnitRawInputIso,
    normalizedCoefficientInputSquareIso, tensorCoefficientNormalization,
    pullbackInputSquareIso, originalCoefficientInputSquareIso,
    boundedFlatPerfectPseudofunctor_map_eq, boundedFlatPerfectPseudofunctor_mapComp_eq,
    Iso.trans_assoc] using hs

private theorem whiskerIso_eq_of_eq {C D E F : Type*}
    [Category* C] [Category* D] [Category* E] [Category* F]
    {G H : C ⥤ D} (e e' : G ≅ H) (h : e = e') (L : E ⥤ C) (R : D ⥤ F) :
    isoWhiskerRight (isoWhiskerLeft L e) R =
      isoWhiskerLeft L (isoWhiskerRight e' R) := by
  subst e'
  rfl

/-- The exact original raw square is retained by the common-universe Model lift. -/
theorem tensorUnitRawModelInputIso_eq :
    tensorUnitRawModelInputIso p q a b h =
      smallCoefficientInputSquareIso boundedFlatPerfectPseudofunctor
        p.op a.op b.op q.op (congrArg (fun f : C ⟶ B => f.op) h)
        (tensorCoefficientNormalization p) (evaluationRawNormalization a)
        (evaluationRawNormalization b) (tensorCoefficientNormalization q) := by
  exact whiskerIso_eq_of_eq _ _ (tensorUnitRawNormalizedInputIso_eq p q a b h)
    AsSmall.down.{u, u + 1, 0} AsSmall.up.{u, u + 1, 0}

end Quillen.PerfectComplexes
