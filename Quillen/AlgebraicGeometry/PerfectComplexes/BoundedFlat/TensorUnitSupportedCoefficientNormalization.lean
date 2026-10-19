/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitSupportedCoefficientAutomorphism
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitSupportedPairNaturality

/-!
# Original zero normalization of the genuine first coefficient tensor slice

First use the actual tensor-zero row isomorphisms. Then use precisely the existing canonical
zero normalization of the tensor functor in the second input. Conjugating the independently
constructed first-row automorphism by these displayed isomorphisms gives the original normalized
tensor transformation, followed by the original one-row embedding. The entire fixed-cell prism
therefore agrees with the original suspension-row cylinder before realization.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
open Quillen.Waldhausen Quillen.Waldhausen.QuotientRows Quillen.Waldhausen.IteratedS
open scoped Simplicial
universe u
namespace Quillen.PerfectComplexes
variable {S T : Scheme.OpenPairs.{u}} (p : S ⟶ T)

/-- The actual tensor functor with exactly its original chosen-zero normalization. -/
def tensorSupportedPairNormalizedFunctor :
    (boundedFlatPerfectSupported T.obj.hom).FullSubcategory ⥤
      (boundedFlatPerfectSupported S.obj.hom).FullSubcategory :=
  Quillen.rebaseFunctor (tensorSupportedPairFunctor p)
    (boundedFlatPerfectSupportedWaldhausen T.obj.hom).zero
    (boundedFlatPerfectSupportedWaldhausen S.obj.hom).zero
    (((tensorSupportedPair_exact p).zero
      (boundedFlatPerfectSupportedWaldhausen T.obj.hom).isZero).iso
      (boundedFlatPerfectSupportedWaldhausen S.obj.hom).isZero)

/-- The actual supported functor retains its original chosen-zero normalization iso. -/
def tensorSupportedPairNormalization :=
  Quillen.rebaseFunctorIso (tensorSupportedPairFunctor p)
    (boundedFlatPerfectSupportedWaldhausen T.obj.hom).zero
    (boundedFlatPerfectSupportedWaldhausen S.obj.hom).zero
    (((tensorSupportedPair_exact p).zero
      (boundedFlatPerfectSupportedWaldhausen T.obj.hom).isZero).iso
      (boundedFlatPerfectSupportedWaldhausen S.obj.hom).isZero)

/-- The two genuine coefficient-zero comparisons followed by the original input normalization. -/
def tensorSupportedPairFirstRowNormalization :
    boundedFlatPerfectSupportedPullback p ⋙
      boundedFlatPerfectSupportedTensorUnitFirstRow S.obj.hom ≅
      tensorSupportedPairNormalizedFunctor p ⋙
      oneEmbedding (boundedFlatPerfectSupportedWaldhausen S.obj.hom) :=
  Functor.isoWhiskerLeft (boundedFlatPerfectSupportedPullback p)
    (supportedTensorUnitFirstRowIso S.obj.hom) ≪≫
    Functor.isoWhiskerRight (tensorSupportedPairNormalization p)
    (oneEmbedding (boundedFlatPerfectSupportedWaldhausen S.obj.hom))

/-- Normalize the actual coefficient-row automorphism by those explicitly displayed comparisons. -/
def tensorSupportedPairFirstRowNormalizedAutomorphism (r : (Γ(S.obj.right, ⊤))ˣ) :
    tensorSupportedPairNormalizedFunctor p ⋙
      oneEmbedding (boundedFlatPerfectSupportedWaldhausen S.obj.hom) ≅
      tensorSupportedPairNormalizedFunctor p ⋙
      oneEmbedding (boundedFlatPerfectSupportedWaldhausen S.obj.hom) :=
  (tensorSupportedPairFirstRowNormalization p).symm ≪≫
    Functor.isoWhiskerLeft (boundedFlatPerfectSupportedPullback p)
    (supportedTensorUnitFirstRowAutomorphism S.obj.hom r) ≪≫
    tensorSupportedPairFirstRowNormalization p

/-- The entire normalized first-row arrow is the original normalized tensor arrow, row by row. -/
theorem tensorSupportedPairFirstRowNormalizedAutomorphism_hom (r : (Γ(S.obj.right, ⊤))ˣ) :
    (tensorSupportedPairFirstRowNormalizedAutomorphism p r).hom =
      whiskerRight (normalizedWeakTransformation (tensorSupportedPair_exact p)
        (tensorSupportedPair_exact p)
        (tensorSupportedPairAutomorphism p r).hom)
        (oneEmbedding (boundedFlatPerfectSupportedWaldhausen S.obj.hom)) := by
  have h := supportedTensorUnitFirstRowAutomorphism_comparison S.obj.hom r
  apply NatTrans.ext
  funext K
  have hK := NatTrans.congr_app h ((boundedFlatPerfectSupportedPullback p).obj K)
  dsimp only [NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app] at hK
  dsimp only [tensorSupportedPairFirstRowNormalizedAutomorphism,
    tensorSupportedPairFirstRowNormalization,
    Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv, Functor.whiskerRight_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app]
  simp only [Category.assoc]
  rw [← Category.assoc
    ((supportedTensorUnitFirstRowAutomorphism S.obj.hom r).hom.app
      ((boundedFlatPerfectSupportedPullback p).obj K))
    ((supportedTensorUnitFirstRowIso S.obj.hom).hom.app
      ((boundedFlatPerfectSupportedPullback p).obj K))
    ((oneEmbedding (boundedFlatPerfectSupportedWaldhausen S.obj.hom)).map
      ((tensorSupportedPairNormalization p).hom.app K)),
    hK]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  simp only [normalizedWeakTransformation, NatTrans.comp_app,
    Functor.map_comp]
  rfl

/-- The actual normalized coefficient arrow uncurried against the second grid, then first-row
restriction. Both original coefficient parameters remain independent. -/
def tensorSupportedPairNormalizedCoefficientPrism (r : (Γ(S.obj.right, ⊤))ˣ)
    {k n m : SimplexCategory}
    (A : Grid₂ n m ⥤ (boundedFlatPerfectSupported T.obj.hom).FullSubcategory)
    (τ : m ⟶ ⦋1⦌) (θ : k ⟶ ⦋1⦌) :
    Grid₂ n m ⥤ Obj (boundedFlatPerfectSupportedWaldhausen S.obj.hom) k :=
  ((nerveTimeFunctor n τ).prod' A ⋙ Functor.uncurry.obj
    (ComposableArrows.mk₁ (tensorSupportedPairFirstRowNormalizedAutomorphism p r).hom)) ⋙
      reindex (boundedFlatPerfectSupportedWaldhausen S.obj.hom) θ

/-- The whole normalized fixed-cell slice equals the original tensor cylinder and suspension row.
-/
theorem tensorSupportedPairNormalizedCoefficientPrism_eq (r : (Γ(S.obj.right, ⊤))ˣ)
    {k n m : SimplexCategory}
    (A : Grid₂ n m ⥤ (boundedFlatPerfectSupported T.obj.hom).FullSubcategory)
    (τ : m ⟶ ⦋1⦌) (θ : k ⟶ ⦋1⦌) :
    tensorSupportedPairNormalizedCoefficientPrism p r A τ θ =
      nerveCylinderDiagram (whiskerLeft A
        (normalizedWeakTransformation (tensorSupportedPair_exact p)
          (tensorSupportedPair_exact p)
          (tensorSupportedPairAutomorphism p r).hom)) τ ⋙
        suspensionRow (boundedFlatPerfectSupportedWaldhausen S.obj.hom) θ := by
  unfold tensorSupportedPairNormalizedCoefficientPrism
  rw [← nerveCylinderDiagram_whiskerLeft, tensorSupportedPairFirstRowNormalizedAutomorphism_hom]
  rw [show whiskerLeft A (whiskerRight
      (normalizedWeakTransformation (tensorSupportedPair_exact p)
        (tensorSupportedPair_exact p)
        (tensorSupportedPairAutomorphism p r).hom)
      (oneEmbedding (boundedFlatPerfectSupportedWaldhausen S.obj.hom))) =
    whiskerRight (whiskerLeft A
      (normalizedWeakTransformation (tensorSupportedPair_exact p)
        (tensorSupportedPair_exact p)
        (tensorSupportedPairAutomorphism p r).hom))
      (oneEmbedding (boundedFlatPerfectSupportedWaldhausen S.obj.hom)) from rfl]
  rw [iteratedNerveCylinderDiagram_postcomp]
  rfl

end Quillen.PerfectComplexes
