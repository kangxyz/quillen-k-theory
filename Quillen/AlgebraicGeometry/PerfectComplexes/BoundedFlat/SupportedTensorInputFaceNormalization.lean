/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedGeometricForgetNormalizedSquare
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedTensorForgetNormalizedRectangle
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitSupportedRawModelInputSquare
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitRawModelInputSquare
public import Quillen.Aglib.CategoryTheory.Functor.IsoPathNormalization

/-! # The six original tensor input faces and their specified edge normalizations

Each face is identified with conjugation by the actual two path normalizations. The independent
raw square definitions and all selected-zero comparison isomorphisms are retained exactly.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.SupportedTensorEvaluation
open GlobalSectionChangeIndex

/-- The original support inclusion rebased at the two originally selected zero objects. -/
def supportedForgetNormalizedFunctor {X : Scheme.{u}ᵒᵖ} {U : Scheme.{u}}
    (j : U ⟶ X.unop) [IsOpenImmersion j] :=
  Quillen.rebaseFunctor (tensorCoefficientSupportedForget j)
    (boundedFlatPerfectSupportedWaldhausen j).zero
    (boundedFlatPerfectWaldhausen X.unop).zero
    (((tensorCoefficientSupportedForget_exact j).zero
      (boundedFlatPerfectSupportedWaldhausen j).isZero).iso
      (boundedFlatPerfectWaldhausen X.unop).isZero)

/-- The original Model forget map uses precisely that original common-universe functor. -/
theorem supportedForgetModel_functor {X : Scheme.{u}ᵒᵖ} {U : Scheme.{u}}
    (j : U ⟶ X.unop) [IsOpenImmersion j] :
    (tensorCoefficientSupportedForgetModel j).functor =
      smallModelFunctor (supportedForgetNormalizedFunctor j) := rfl

/-- The original tensor forgetting face is the specified four-edge normalization. -/
theorem tensorForgetNormalizedIso_eq_face {A B : Scheme.OpenPairs.{u}} (p : A ⟶ B) :
    tensorForgetNormalizedIso p = faceNormalization (tensorSupportedPairForgetIso p)
      (tensorSupportedPairNormalization p)
      (forgetRawNormalization (X := op A.obj.right) A.obj.hom)
      (forgetRawNormalization (X := op B.obj.right) B.obj.hom)
      (tensorUnitPullbackNormalization p.hom.right) := rfl

/-- The actual geometric forgetting face keeps its four independently selected zero paths. -/
theorem geometricForgetNormalizedIso_eq_face {A B : Scheme.OpenPairs.{u}} (p : A ⟶ B) :
    geometricForgetNormalizedIso p = faceNormalization (supportedPullbackForgetIso p)
      (evaluationRawNormalization p)
      (forgetRawNormalization (X := op A.obj.right) A.obj.hom)
      (forgetRawNormalization (X := op B.obj.right) B.obj.hom)
      (GlobalSectionChangeIndex.evaluationRawNormalization p.hom.right) := rfl

/-- The independent supported raw tensor input square has exactly its original four-edge word. -/
theorem tensorSupportedRawNormalizedInputIso_eq_face {A B C D : Scheme.OpenPairs.{u}}
    (p : A ⟶ B) (q : C ⟶ D) (a : C ⟶ A) (b : D ⟶ B) (h : a ≫ p = q ≫ b) :
    tensorSupportedRawNormalizedInputIso p q a b h =
      faceNormalization (tensorSupportedRawInputIso p q a b h)
        (tensorSupportedPairNormalization p) (evaluationRawNormalization a)
        (evaluationRawNormalization b) (tensorSupportedPairNormalization q) :=
  (faceNormalization_eq_alternate _ _ _ _ _).symm

/-- The independent ambient raw square retains the corresponding original normalization word. -/
theorem tensorUnitRawNormalizedInputIso_eq_face {A B C D : Scheme.{u}}
    (p : A ⟶ B) (q : C ⟶ D) (a : C ⟶ A) (b : D ⟶ B) (h : a ≫ p = q ≫ b) :
    tensorUnitRawNormalizedInputIso p q a b h =
      faceNormalization (tensorUnitRawInputIso p q a b h)
        (tensorUnitPullbackNormalization p) (GlobalSectionChangeIndex.evaluationRawNormalization a)
        (GlobalSectionChangeIndex.evaluationRawNormalization b)
        (tensorUnitPullbackNormalization q) :=
  (faceNormalization_eq_alternate _ _ _ _ _).symm

end Quillen.PerfectComplexes.SupportedTensorEvaluation
