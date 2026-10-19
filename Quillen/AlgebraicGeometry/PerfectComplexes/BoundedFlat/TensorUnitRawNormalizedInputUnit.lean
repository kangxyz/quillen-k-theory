/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitRawModelInputSquare
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalUnitReferenceNaturality

/-! # Original multiplication on the based genuine tensor input square

The conjugated genuine tensor multiplication is identified using its original scalar equation
and naturality of the actual chosen-zero normalization. The raw input square remains unchanged.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS Quillen.FunctorIdentityAutomorphism
universe u
namespace Quillen.PerfectComplexes

/-- Genuine tensor multiplication after its specified zero normalization is the same scalar. -/
theorem tensorUnitNormalizedTransformation_scalar {X Y : Scheme.{u}} (f : X ⟶ Y)
    (r : (Γ(X, ⊤))ˣ) :
    normalizedWeakTransformation (boundedFlatPerfectTensorUnitPullback_exact f)
        (boundedFlatPerfectTensorUnitPullback_exact f)
        (boundedFlatPerfectTensorUnitPullbackAutomorphism f r).hom =
      (onFunctor _ (boundedFlatPerfectGlobalUnitIso X r)).hom := by
  apply NatTrans.ext
  funext K
  change (tensorUnitPullbackNormalization f).inv.app K ≫
      (boundedFlatPerfectTensorUnitPullbackAutomorphism f r).hom.app K ≫
        (tensorUnitPullbackNormalization f).hom.app K = _
  rw [ParameterTensorEvaluationRow.tensorAutomorphism_scalar]
  have hn := (boundedFlatPerfectGlobalUnitIso X r).hom.naturality
    ((tensorUnitPullbackNormalization f).hom.app K)
  simp only [Functor.id_map, Functor.id_obj] at hn
  change _ = (boundedFlatPerfectGlobalUnitIso X r).hom.app _
  rw [← hn, Iso.inv_hom_id_app_assoc]
  rfl

/-- The full original tensor action respects the raw square after all four based normalizations.
-/
theorem tensorUnitRawNormalizedInputIso_unit
    {A B C D : Scheme.{u}} (p : A ⟶ B) (q : C ⟶ D)
    (a : C ⟶ A) (b : D ⟶ B) (h : a ≫ p = q ≫ b) (r : (Γ(A, ⊤))ˣ) :
    whiskerRight
        (normalizedWeakTransformation (boundedFlatPerfectTensorUnitPullback_exact p)
          (boundedFlatPerfectTensorUnitPullback_exact p)
          (boundedFlatPerfectTensorUnitPullbackAutomorphism p r).hom)
        (boundedFlatNormalizedPullback a) ≫ (tensorUnitRawNormalizedInputIso p q a b h).hom =
      (tensorUnitRawNormalizedInputIso p q a b h).hom ≫
        whiskerLeft (boundedFlatNormalizedPullback b)
          (normalizedWeakTransformation (boundedFlatPerfectTensorUnitPullback_exact q)
            (boundedFlatPerfectTensorUnitPullback_exact q)
            (boundedFlatPerfectTensorUnitPullbackAutomorphism q
              (Units.map a.appTop.hom.toMonoidHom r)).hom) := by
  rw [tensorUnitNormalizedTransformation_scalar, tensorUnitNormalizedTransformation_scalar]
  exact onFunctor_whisker_square _ _ _ _ (tensorUnitRawNormalizedInputIso p q a b h).hom
    (boundedFlatPerfectGlobalUnitIso A r)
    (boundedFlatPerfectGlobalUnitIso C (Units.map a.appTop.hom.toMonoidHom r))
    (GlobalUnitReferenceNaturality.normalizedPullback_preserves a r).whisker

end Quillen.PerfectComplexes
