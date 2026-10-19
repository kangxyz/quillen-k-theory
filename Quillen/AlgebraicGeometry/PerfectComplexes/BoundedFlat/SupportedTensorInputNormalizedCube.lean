/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedTensorInputFaceNormalization
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitSupportedRawInputForgetSquare
public import Quillen.Aglib.CategoryTheory.Functor.IsoCubeNormalization

/-! # The entire original supported tensor cube after geometric zero normalization

All twelve edge isomorphisms are the original tensor, pullback and support-inclusion zero
normalizations. The independent source and target raw squares and the four genuine forgetting
faces remain explicit. Their whole cube is transported from the original raw cube.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
universe u
namespace Quillen.PerfectComplexes.SupportedTensorEvaluation
open GlobalSectionChangeIndex
private theorem cubeFaces_congr
    {C₀ C₁ C₂ C₃ D₀ D₁ D₂ D₃ : Type u}
    [Category C₀] [Category C₁] [Category C₂] [Category C₃]
    [Category D₀] [Category D₁] [Category D₂] [Category D₃]
    {P : C₀ ⥤ C₁} {A : C₁ ⥤ C₂} {B : C₀ ⥤ C₃} {Q : C₃ ⥤ C₂}
    {p : D₀ ⥤ D₁} {a : D₁ ⥤ D₂} {b : D₀ ⥤ D₃} {q : D₃ ⥤ D₂}
    {E₀ : C₀ ⥤ D₀} {E₁ : C₁ ⥤ D₁} {E₂ : C₂ ⥤ D₂} {E₃ : C₃ ⥤ D₃}
    {R R' : P ⋙ A ≅ B ⋙ Q} {r r' : p ⋙ a ≅ b ⋙ q}
    {sP sP' : P ⋙ E₁ ≅ E₀ ⋙ p} {sA sA' : A ⋙ E₂ ≅ E₁ ⋙ a}
    {sB sB' : B ⋙ E₃ ≅ E₀ ⋙ b} {sQ sQ' : Q ⋙ E₂ ≅ E₃ ⋙ q}
    (hR : R = R') (hr : r = r') (hP : sP = sP') (hA : sA = sA')
    (hB : sB = sB') (hQ : sQ = sQ')
    (h : isoWhiskerRight R E₂ ≪≫ isoSquareRoute sB sQ =
      isoSquareRoute sP sA ≪≫ isoWhiskerLeft E₀ r) :
    isoWhiskerRight R' E₂ ≪≫ isoSquareRoute sB' sQ' =
      isoSquareRoute sP' sA' ≪≫ isoWhiskerLeft E₀ r' := by
  cases hR
  cases hr
  cases hP
  cases hA
  cases hB
  cases hQ
  exact h

variable {A B C D : Scheme.OpenPairs.{u}}
  (p : A ⟶ B) (q : C ⟶ D) (a : C ⟶ A) (b : D ⟶ B) (h : a ≫ p = q ≫ b)

/-- The independently normalized tensor-first route. -/
def normalizedInputForgetLeftRoute :=
  isoSquareRoute (tensorForgetNormalizedIso p) (geometricForgetNormalizedIso a)

/-- The independently normalized geometric-input-first route. -/
def normalizedInputForgetRightRoute :=
  isoSquareRoute (geometricForgetNormalizedIso b) (tensorForgetNormalizedIso q)

/-- The complete original raw cube survives every independently chosen geometric zero rebase. -/
theorem tensorSupportedNormalizedInputForgetCube :
    isoWhiskerRight (tensorSupportedRawNormalizedInputIso p q a b h)
        (supportedForgetNormalizedFunctor (X := op C.obj.right) C.obj.hom) ≪≫
        normalizedInputForgetRightRoute q b =
      normalizedInputForgetLeftRoute p a ≪≫
        isoWhiskerLeft (supportedForgetNormalizedFunctor (X := op B.obj.right) B.obj.hom)
          (tensorUnitRawNormalizedInputIso p.hom.right q.hom.right a.hom.right b.hom.right
            (congrArg (fun f : C ⟶ B => f.hom.right) h)) := by
  have hAmbient := tensorUnitRawNormalizedInputIso_eq_face
    p.hom.right q.hom.right a.hom.right b.hom.right
    (congrArg (fun f : C ⟶ B => f.hom.right) h)
  have hc := isoCube_faceNormalization
    (tensorSupportedRawInputIso p q a b h)
    (tensorUnitRawInputIso p.hom.right q.hom.right a.hom.right b.hom.right
      (congrArg (fun f : C ⟶ B => f.hom.right) h))
    (tensorSupportedPairForgetIso p) (supportedPullbackForgetIso a)
    (supportedPullbackForgetIso b) (tensorSupportedPairForgetIso q)
    (tensorSupportedRawInputForgetSquare p q a b h)
    (tensorSupportedPairNormalization p) (evaluationRawNormalization a)
    (evaluationRawNormalization b) (tensorSupportedPairNormalization q)
    (tensorUnitPullbackNormalization p.hom.right)
    (GlobalSectionChangeIndex.evaluationRawNormalization a.hom.right)
    (GlobalSectionChangeIndex.evaluationRawNormalization b.hom.right)
    (tensorUnitPullbackNormalization q.hom.right)
    (forgetRawNormalization (X := op B.obj.right) B.obj.hom)
    (forgetRawNormalization (X := op A.obj.right) A.obj.hom)
    (forgetRawNormalization (X := op C.obj.right) C.obj.hom)
    (forgetRawNormalization (X := op D.obj.right) D.obj.hom)
  exact cubeFaces_congr
    (tensorSupportedRawNormalizedInputIso_eq_face p q a b h).symm hAmbient.symm
    (tensorForgetNormalizedIso_eq_face p).symm
    (geometricForgetNormalizedIso_eq_face a).symm
    (geometricForgetNormalizedIso_eq_face b).symm
    (tensorForgetNormalizedIso_eq_face q).symm hc


end Quillen.PerfectComplexes.SupportedTensorEvaluation
