/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassNegativeTargetChartAttachment
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.NativeReferenceWordCoherence
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSeedTargetCanonicalAnchor

/-! The actual chart square agrees with the prescribed canonical normalization anchor. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u v
namespace Quillen.PerfectComplexes.CoefficientBassNegativeTargetCanonicalAnchor
open BassReferenceMerge
variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (f : a ⟶ b)
variable {X : Scheme.{u}} (h : space (op P, (polynomialUnderFunctor R).obj a) ⟶ X)
local notation "l" => coefficientMap P (CategoryTheory.Functor.map (laurentUnderFunctor R) f)
local notation "m" => coefficientMap P (CategoryTheory.Functor.map (polynomialUnderFunctor R) f)
local notation "ja" => laurentMinus P a
local notation "jb" => laurentMinus P b
local notation "N" => boundedFlatNormalizedPullback
local notation "C" => boundedFlatNormalizedPullbackCompIso

/-- The literal coefficient chart square, with its declared geometric endpoint maps. -/
theorem chart_square : l ≫ ja = jb ≫ m :=
  coefficientMap_naturality P (underToLaurentInvert R) f

/-- The actual complete geometric equality keeps the original source reference h. -/
theorem total_square : l ≫ ja ≫ h = jb ≫ m ≫ h :=
  (Category.assoc l ja h).symm.trans
    ((congrArg (fun k ↦ k ≫ h) (chart_square P f)).trans
      (Category.assoc jb m h))

open Quillen.Waldhausen.IteratedS BassH0Merge CoefficientBassNegativeTargetChartAttachment

/-- The prescribed target anchor, retaining the original geometric transport and normalization. -/
def canonicalAnchor :
    (normalizedMap (l ≫ ja ≫ h)).functor ≅
      (normalizedMap (m ≫ h) ≫ Jb P (b := b)).functor :=
  eqToIso (congrArg (fun k ↦ (normalizedMap k).functor) (total_square P f h)) ≪≫
    BinaryNormalizationSimplex.total jb (m ≫ h)

/-- The actual small-model chart-square iso is the small image of its original raw normalization. -/
theorem rightIso_small : rightIso P f =
    smallIso (eqToIso (congrArg N (chart_square P f)) ≪≫ C jb m) := by
  rw [smallIso_trans, smallIso_eqToIso]
  rfl

private theorem flatten_anchor {C₀ A₀ B₀ A₁ B₁ : Type*}
    [Category* C₀] [Category* A₀] [Category* B₀] [Category* A₁] [Category* B₁]
    (F : C₀ ⥤ A₀) (G : C₀ ⥤ B₀) (J : A₀ ⥤ B₀) (L : B₀ ⥤ B₁)
    (H : A₀ ⥤ B₁) (M : A₀ ⥤ A₁) (K : A₁ ⥤ B₁)
    (e : G ≅ F ⋙ J) (lft : H ≅ J ⋙ L) (rgt : H ≅ M ⋙ K) :
    (isoWhiskerRight e L ≪≫ Functor.associator F J L ≪≫
      isoWhiskerLeft F lft.symm) ≪≫ isoWhiskerLeft F rgt ≪≫
        (Functor.associator F M K).symm =
      isoWhiskerRight e L ≪≫ isoWhiskerLeft F (lft.symm ≪≫ rgt) := by
  apply Iso.ext
  ext x
  simp

private theorem targetAnchor_flat {V : Model.{u + 1}}
    (D : V ⟶ modelOf (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a))))
    (G : V ⟶ modelOf (boundedFlatPerfectWaldhausen
      (space (op P, (laurentUnderFunctor R).obj a))))
    (ε : G.functor ≅ (D ≫ Ja P (a := a)).functor) :
    targetAnchor P f D G ε = isoWhiskerRight ε (L P f).functor ≪≫
      isoWhiskerLeft D.functor ((leftIso P f).symm ≪≫ rightIso P f) :=
  flatten_anchor D.functor G.functor (Ja P).functor (L P f).functor
    (H P f).functor (M P f).functor (Jb P).functor ε (leftIso P f) (rightIso P f)

private theorem total_small {Y Z T : Scheme.{u}} (g : Y ⟶ Z) (k : Z ⟶ T) :
    BinaryNormalizationSimplex.total g k = smallIso (C g k) := rfl

private theorem small_symm {C₀ D₀ : Type u} [Category.{v} C₀] [Category.{v} D₀]
    {F G : C₀ ⥤ D₀} (e : F ≅ G) : (smallIso e).symm = smallIso e.symm := rfl

/-- The canonical small-model target anchor keeps the complete raw normalization reference. -/
theorem canonicalAnchor_small : canonicalAnchor P f h =
    smallIso (eqToIso (congrArg N (total_square P f h)) ≪≫ C jb (m ≫ h)) := by
  rw [smallIso_trans, smallIso_eqToIso]
  rfl

private theorem ordinary_small_anchor :
    smallIso (C l (ja ≫ h)) ≪≫
      smallIso (isoWhiskerRight (C ja h) (N l)) ≪≫
      smallIso (isoWhiskerLeft (N h) ((C l ja).symm ≪≫
        (eqToIso (congrArg N (chart_square P f)) ≪≫ C jb m))) =
    smallIso (eqToIso (congrArg N (total_square P f h)) ≪≫ C jb (m ≫ h)) ≪≫
      smallIso (isoWhiskerRight (C m h) (N jb)) :=
  CoefficientBassSeedTargetCanonicalAnchor.normalized_small_square l ja jb m h
    (chart_square P f) (total_square P f h)

/-- The actual target chart attachment agrees with the prescribed canonical small-model anchor. -/
theorem ordinary_model_anchor :
    BinaryNormalizationSimplex.total l (ja ≫ h) ≪≫
      targetAnchor P f (normalizedMap h) (normalizedMap (ja ≫ h))
        (BinaryNormalizationSimplex.total ja h) =
      canonicalAnchor P f h ≪≫
        isoWhiskerRight (BinaryNormalizationSimplex.total m h) (Jb P (b := b)).functor := by
  rw [targetAnchor_flat, rightIso_small, canonicalAnchor_small, leftIso]
  simp only [total_small]
  erw [small_symm (C l ja)]
  erw [smallIso_postcomp, smallIso_postcomp]
  rw [← smallIso_trans]
  erw [smallIso_precomp]
  exact ordinary_small_anchor P f h

end Quillen.PerfectComplexes.CoefficientBassNegativeTargetCanonicalAnchor
