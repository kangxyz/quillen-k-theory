/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitCoefficientPrismNaturality
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitPullbackPrism

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
variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The actual tensor functor with exactly its original chosen-zero normalization. -/
def tensorUnitPullbackNormalizedFunctor :
    BoundedFlatPerfect Y ⥤ BoundedFlatPerfect X :=
  Quillen.rebaseFunctor (boundedFlatPerfectTensorUnitPullback f)
    (boundedFlatPerfectWaldhausen Y).zero
    (boundedFlatPerfectWaldhausen X).zero
    (((boundedFlatPerfectTensorUnitPullback_exact f).zero
      (boundedFlatPerfectWaldhausen Y).isZero).iso
      (boundedFlatPerfectWaldhausen X).isZero)

/-- The two genuine coefficient-zero comparisons followed by the original input normalization. -/
def tensorUnitPullbackFirstRowNormalization :
    boundedFlatPerfectPullback f ⋙ boundedFlatPerfectTensorUnitFirstRow X ≅
      tensorUnitPullbackNormalizedFunctor f ⋙ oneEmbedding (boundedFlatPerfectWaldhausen X) :=
  Functor.isoWhiskerLeft (boundedFlatPerfectPullback f) (tensorUnitFirstRowIso X) ≪≫
    Functor.isoWhiskerRight (tensorUnitPullbackNormalization f)
    (oneEmbedding (boundedFlatPerfectWaldhausen X))

/-- Normalize the actual coefficient-row automorphism by those explicitly displayed comparisons. -/
def tensorUnitPullbackFirstRowNormalizedAutomorphism (r : (Γ(X, ⊤))ˣ) :
    tensorUnitPullbackNormalizedFunctor f ⋙ oneEmbedding (boundedFlatPerfectWaldhausen X) ≅
      tensorUnitPullbackNormalizedFunctor f ⋙ oneEmbedding (boundedFlatPerfectWaldhausen X) :=
  (tensorUnitPullbackFirstRowNormalization f).symm ≪≫
    Functor.isoWhiskerLeft (boundedFlatPerfectPullback f)
    (tensorUnitFirstRowAutomorphism X r) ≪≫
    tensorUnitPullbackFirstRowNormalization f

/-- The entire normalized first-row arrow is the original normalized tensor arrow, row by row. -/
theorem tensorUnitPullbackFirstRowNormalizedAutomorphism_hom (r : (Γ(X, ⊤))ˣ) :
    (tensorUnitPullbackFirstRowNormalizedAutomorphism f r).hom =
      whiskerRight (normalizedWeakTransformation (boundedFlatPerfectTensorUnitPullback_exact f)
        (boundedFlatPerfectTensorUnitPullback_exact f)
        (boundedFlatPerfectTensorUnitPullbackAutomorphism f r).hom)
        (oneEmbedding (boundedFlatPerfectWaldhausen X)) := by
  have h := tensorUnitFirstRowAutomorphism_comparison X r
  apply NatTrans.ext
  funext K
  have hK := NatTrans.congr_app h ((boundedFlatPerfectPullback f).obj K)
  dsimp only [NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app] at hK
  dsimp only [tensorUnitPullbackFirstRowNormalizedAutomorphism,
    tensorUnitPullbackFirstRowNormalization,
    Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv, Functor.whiskerRight_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app]
  simp only [Category.assoc]
  rw [← Category.assoc
    ((tensorUnitFirstRowAutomorphism X r).hom.app ((boundedFlatPerfectPullback f).obj K))
    ((tensorUnitFirstRowIso X).hom.app ((boundedFlatPerfectPullback f).obj K))
    ((oneEmbedding (boundedFlatPerfectWaldhausen X)).map
      ((tensorUnitPullbackNormalization f).hom.app K)),
    hK]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  simp only [normalizedWeakTransformation, NatTrans.comp_app,
    Functor.map_comp]
  rfl

/-- The actual normalized coefficient arrow uncurried against the second grid, then first-row
restriction. Both original coefficient parameters remain independent. -/
def tensorUnitPullbackNormalizedCoefficientPrism (r : (Γ(X, ⊤))ˣ)
    {k n m : SimplexCategory} (A : Grid₂ n m ⥤ BoundedFlatPerfect Y)
    (τ : m ⟶ ⦋1⦌) (θ : k ⟶ ⦋1⦌) :
    Grid₂ n m ⥤ Obj (boundedFlatPerfectWaldhausen X) k :=
  ((nerveTimeFunctor n τ).prod' A ⋙ Functor.uncurry.obj
    (ComposableArrows.mk₁ (tensorUnitPullbackFirstRowNormalizedAutomorphism f r).hom)) ⋙
      reindex (boundedFlatPerfectWaldhausen X) θ

/-- The whole normalized fixed-cell slice equals the original tensor cylinder and suspension row.
-/
theorem tensorUnitPullbackNormalizedCoefficientPrism_eq (r : (Γ(X, ⊤))ˣ)
    {k n m : SimplexCategory} (A : Grid₂ n m ⥤ BoundedFlatPerfect Y)
    (τ : m ⟶ ⦋1⦌) (θ : k ⟶ ⦋1⦌) :
    tensorUnitPullbackNormalizedCoefficientPrism f r A τ θ =
      nerveCylinderDiagram (whiskerLeft A
        (normalizedWeakTransformation (boundedFlatPerfectTensorUnitPullback_exact f)
          (boundedFlatPerfectTensorUnitPullback_exact f)
          (boundedFlatPerfectTensorUnitPullbackAutomorphism f r).hom)) τ ⋙
        suspensionRow (boundedFlatPerfectWaldhausen X) θ := by
  unfold tensorUnitPullbackNormalizedCoefficientPrism
  rw [← nerveCylinderDiagram_whiskerLeft, tensorUnitPullbackFirstRowNormalizedAutomorphism_hom]
  rw [show whiskerLeft A (whiskerRight
      (normalizedWeakTransformation (boundedFlatPerfectTensorUnitPullback_exact f)
        (boundedFlatPerfectTensorUnitPullback_exact f)
        (boundedFlatPerfectTensorUnitPullbackAutomorphism f r).hom)
      (oneEmbedding (boundedFlatPerfectWaldhausen X))) =
    whiskerRight (whiskerLeft A
      (normalizedWeakTransformation (boundedFlatPerfectTensorUnitPullback_exact f)
        (boundedFlatPerfectTensorUnitPullback_exact f)
        (boundedFlatPerfectTensorUnitPullbackAutomorphism f r).hom))
      (oneEmbedding (boundedFlatPerfectWaldhausen X)) from rfl]
  rw [iteratedNerveCylinderDiagram_postcomp]
  rfl

end Quillen.PerfectComplexes
