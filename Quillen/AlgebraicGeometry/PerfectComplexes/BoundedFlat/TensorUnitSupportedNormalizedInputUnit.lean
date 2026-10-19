/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitSupportedRawModelInputSquare
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitSupportedModelUnit
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedGlobalUnitIdentityOperation

/-! # Genuine supported multiplication on the normalized input square

The actual tensor multiplication survives the original chosen-zero rebases and common-universe
transport. Its whole input square retains the original pulled-back scalar.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS Quillen.FunctorIdentityAutomorphism
universe u
namespace Quillen.PerfectComplexes.SupportedTensorEvaluation

/-- The original supported geometric pullback with its originally chosen zero rebase. -/
abbrev normalizedPullback {A B : Scheme.OpenPairs.{u}} (p : A ⟶ B) :=
  Quillen.rebaseFunctor (boundedFlatPerfectSupportedPullback p)
    (boundedFlatPerfectSupportedWaldhausen B.obj.hom).zero
    (boundedFlatPerfectSupportedWaldhausen A.obj.hom).zero
    (((boundedFlatPerfectSupportedPullback_exact p).zero
      (boundedFlatPerfectSupportedWaldhausen B.obj.hom).isZero).iso
      (boundedFlatPerfectSupportedWaldhausen A.obj.hom).isZero)

/-- The original geometric normalization preserves the actual forward pulled-back scalar. -/
theorem normalizedPullback_preserves {A B : Scheme.OpenPairs.{u}} (p : A ⟶ B)
    (r : (Γ(B.obj.right, ⊤))ˣ) :
    Preserves (normalizedPullback p) (boundedFlatPerfectSupportedGlobalUnitIso B.obj.hom r)
      (boundedFlatPerfectSupportedGlobalUnitIso A.obj.hom
        (Units.map p.hom.right.appTop.hom.toMonoidHom r)) :=
  rebase_preserves _ _ _ _ _ _ (SupportedGlobalUnitIdentityOperation.pullback_preserves p r)

/-- Tensor multiplication after its specified supported zero normalization is the same scalar. -/
theorem normalizedTensorTransformation_scalar {A B : Scheme.OpenPairs.{u}} (p : A ⟶ B)
    (r : (Γ(A.obj.right, ⊤))ˣ) :
    normalizedWeakTransformation (tensorSupportedPair_exact p) (tensorSupportedPair_exact p)
        (tensorSupportedPairAutomorphism p r).hom =
      (onFunctor (tensorSupportedPairNormalizedFunctor p)
        (boundedFlatPerfectSupportedGlobalUnitIso A.obj.hom r)).hom := by
  apply NatTrans.ext
  funext K
  change (tensorSupportedPairNormalization p).inv.app K ≫
      (tensorSupportedPairAutomorphism p r).hom.app K ≫
        (tensorSupportedPairNormalization p).hom.app K = _
  rw [tensorAutomorphism_scalar]
  have hn := (boundedFlatPerfectSupportedGlobalUnitIso A.obj.hom r).hom.naturality
    ((tensorSupportedPairNormalization p).hom.app K)
  simp only [Functor.id_map, Functor.id_obj] at hn
  change _ = (boundedFlatPerfectSupportedGlobalUnitIso A.obj.hom r).hom.app _
  rw [← hn, Iso.inv_hom_id_app_assoc]
  rfl

/-- The genuine tensor input square keeps its multiplication after all four actual rebases. -/
theorem normalizedInputIso_unit {A B C D : Scheme.OpenPairs.{u}}
    (p : A ⟶ B) (q : C ⟶ D) (a : C ⟶ A) (b : D ⟶ B) (h : a ≫ p = q ≫ b)
    (r : (Γ(A.obj.right, ⊤))ˣ) :
    whiskerRight
        (normalizedWeakTransformation (tensorSupportedPair_exact p) (tensorSupportedPair_exact p)
          (tensorSupportedPairAutomorphism p r).hom) (normalizedPullback a) ≫
        (tensorSupportedRawNormalizedInputIso p q a b h).hom =
      (tensorSupportedRawNormalizedInputIso p q a b h).hom ≫
        whiskerLeft (normalizedPullback b)
          (normalizedWeakTransformation (tensorSupportedPair_exact q) (tensorSupportedPair_exact q)
            (tensorSupportedPairAutomorphism q
              (Units.map a.hom.right.appTop.hom.toMonoidHom r)).hom) := by
  rw [normalizedTensorTransformation_scalar, normalizedTensorTransformation_scalar]
  exact onFunctor_whisker_square _ _ _ _ (tensorSupportedRawNormalizedInputIso p q a b h).hom
    (boundedFlatPerfectSupportedGlobalUnitIso A.obj.hom r)
    (boundedFlatPerfectSupportedGlobalUnitIso C.obj.hom
      (Units.map a.hom.right.appTop.hom.toMonoidHom r))
    (normalizedPullback_preserves a r).whisker

end Quillen.PerfectComplexes.SupportedTensorEvaluation
