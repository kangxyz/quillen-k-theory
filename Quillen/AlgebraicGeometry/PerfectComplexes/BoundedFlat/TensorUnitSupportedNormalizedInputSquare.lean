/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitSupportedRawModelInputSquare
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedNormalizedEvaluationInputRoutes
public import Quillen.Aglib.CategoryTheory.Functor.IsoSquareReplacement

/-! # The independently constructed supported raw square retains all original normalizations

The raw tensor square is identified with the normalized geometric supported square using
exactly the original tensor unitors and all four actual chosen-zero rebases.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes
open GlobalSectionChangeIndex SupportedTensorEvaluation

/-- The actual supported tensor unitor followed by its original tensor zero normalization. -/
def supportedTensorCoefficientNormalization {A B : Scheme.OpenPairs.{u}} (p : A ⟶ B) :=
  (tensorPairUnitor p).symm ≪≫ tensorSupportedPairNormalization p

variable {A B C D : Scheme.OpenPairs.{u}}
  (p : A ⟶ B) (q : C ⟶ D) (a : C ⟶ A) (b : D ⟶ B) (h : a ≫ p = q ≫ b)

/-- The independent supported raw square uses exactly the four specified target normalizations. -/
theorem tensorSupportedRawNormalizedInputIso_eq :
    tensorSupportedRawNormalizedInputIso p q a b h =
      supportedNormalizedInputSquareIso p q a b h
        (supportedTensorCoefficientNormalization p) (evaluationRawNormalization a)
        (evaluationRawNormalization b) (supportedTensorCoefficientNormalization q) := by
  have hs := isoSquareReplacement_normalization
    (tensorPairUnitor p) (tensorPairUnitor q)
    (tensorSupportedPairNormalization p) (evaluationRawNormalization a)
    (evaluationRawNormalization b) (tensorSupportedPairNormalization q)
    (supportedPullbackInputSquareIso p q a b h)
  simpa only [tensorSupportedRawNormalizedInputIso, tensorSupportedRawInputIso,
    supportedNormalizedInputSquareIso, supportedTensorCoefficientNormalization,
    supportedPullbackInputSquareIso, Iso.trans_assoc, Iso.trans_symm,
    isoWhiskerLeft_symm, isoWhiskerRight_symm] using hs

private theorem whiskerIso_eq_of_eq {E F G H : Type*}
    [Category* E] [Category* F] [Category* G] [Category* H]
    {P Q : E ⥤ F} (e e' : P ≅ Q) (h : e = e') (L : G ⥤ E) (R : F ⥤ H) :
    isoWhiskerRight (isoWhiskerLeft L e) R =
      isoWhiskerRight (isoWhiskerLeft L e') R := by
  subst e'
  rfl

/-- The actual common-universe lift preserves the same independently defined supported square. -/
theorem tensorSupportedRawModelInputIso_eq :
    tensorSupportedRawModelInputIso p q a b h =
      supportedSmallInputSquareIso p q a b h
        (supportedTensorCoefficientNormalization p) (evaluationRawNormalization a)
        (evaluationRawNormalization b) (supportedTensorCoefficientNormalization q) := by
  exact whiskerIso_eq_of_eq _ _ (tensorSupportedRawNormalizedInputIso_eq p q a b h)
    AsSmall.down.{u, u + 1, 0} AsSmall.up.{u, u + 1, 0}

end Quillen.PerfectComplexes
