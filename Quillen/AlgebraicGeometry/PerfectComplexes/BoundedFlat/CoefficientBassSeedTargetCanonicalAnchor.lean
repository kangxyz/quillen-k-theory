/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSeedTargetChartAttachment
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.NativeReferenceWordCoherence
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSeedTargetUnitReference

/-! The actual chart square agrees with the prescribed canonical normalization anchor. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u v
namespace Quillen.PerfectComplexes.CoefficientBassSeedTargetCanonicalAnchor
open BassReferenceMerge
private theorem cancel_iso_middle {C₀ : Type*} [Category* C₀]
    {A B C D E : C₀} (i : A ≅ B) (j : B ≅ C) (k : A ≅ D) (l : D ≅ C)
    (m : D ≅ E) (h : i ≪≫ j = k ≪≫ l) :
    i ≪≫ j ≪≫ l.symm ≪≫ m = k ≪≫ m := by
  rw [← Iso.trans_assoc i j, h]
  simp only [Iso.trans_assoc, Iso.self_symm_id_assoc]

private theorem normalized_square {A₀ B₀ A₁ B₁ X : Scheme.{u}}
    (l : B₁ ⟶ B₀) (j₀ : B₀ ⟶ A₀) (j₁ : B₁ ⟶ A₁) (m : A₁ ⟶ A₀)
    (h : A₀ ⟶ X) (sq : l ≫ j₀ = j₁ ≫ m) (tot : l ≫ j₀ ≫ h = j₁ ≫ m ≫ h) :
    boundedFlatNormalizedPullbackCompIso l (j₀ ≫ h) ≪≫
      isoWhiskerRight (boundedFlatNormalizedPullbackCompIso j₀ h)
        (boundedFlatNormalizedPullback l) ≪≫
      isoWhiskerLeft (boundedFlatNormalizedPullback h)
        (boundedFlatNormalizedPullbackCompIso l j₀).symm ≪≫
      isoWhiskerLeft (boundedFlatNormalizedPullback h)
        (eqToIso (congrArg boundedFlatNormalizedPullback sq) ≪≫
          boundedFlatNormalizedPullbackCompIso j₁ m) =
    eqToIso (congrArg boundedFlatNormalizedPullback tot) ≪≫
      boundedFlatNormalizedPullbackCompIso j₁ (m ≫ h) ≪≫
        isoWhiskerRight (boundedFlatNormalizedPullbackCompIso m h)
          (boundedFlatNormalizedPullback j₁) := by
  have first := anchored_factorizations_strict l j₀ h (l ≫ j₀) (j₀ ≫ h)
    (l ≫ j₀ ≫ h) rfl rfl (Category.assoc l j₀ h).symm rfl
  have second := anchored_factorizations_strict j₁ m h (l ≫ j₀) (m ≫ h)
    (l ≫ j₀ ≫ h) sq rfl (Category.assoc l j₀ h).symm tot
  simp only [eqToIso_refl, Iso.refl_trans] at first second
  have hc := cancel_iso_middle (boundedFlatNormalizedPullbackCompIso l (j₀ ≫ h))
    (isoWhiskerRight (boundedFlatNormalizedPullbackCompIso j₀ h)
      (boundedFlatNormalizedPullback l)) (boundedFlatNormalizedPullbackCompIso (l ≫ j₀) h)
    (isoWhiskerLeft (boundedFlatNormalizedPullback h)
      (boundedFlatNormalizedPullbackCompIso l j₀))
    (isoWhiskerLeft (boundedFlatNormalizedPullback h)
      (eqToIso (congrArg boundedFlatNormalizedPullback sq) ≪≫
        boundedFlatNormalizedPullbackCompIso j₁ m)) first.symm
  simpa only [isoWhiskerLeft_symm] using hc.trans second

private theorem normalized_combined_square {A₀ B₀ A₁ B₁ X : Scheme.{u}}
    (l : B₁ ⟶ B₀) (ja : B₀ ⟶ A₀) (jb : B₁ ⟶ A₁) (m : A₁ ⟶ A₀)
    (h : A₀ ⟶ X) (sq : l ≫ ja = jb ≫ m) (tot : l ≫ ja ≫ h = jb ≫ m ≫ h) :
    (boundedFlatNormalizedPullbackCompIso l (ja ≫ h)) ≪≫
      (isoWhiskerRight (boundedFlatNormalizedPullbackCompIso ja h)
        (boundedFlatNormalizedPullback l)) ≪≫
      (isoWhiskerLeft (boundedFlatNormalizedPullback h)
        ((boundedFlatNormalizedPullbackCompIso l ja).symm ≪≫
        (eqToIso (congrArg boundedFlatNormalizedPullback sq) ≪≫
          boundedFlatNormalizedPullbackCompIso jb m))) =
    (eqToIso (congrArg boundedFlatNormalizedPullback tot) ≪≫
      boundedFlatNormalizedPullbackCompIso jb (m ≫ h)) ≪≫
      (isoWhiskerRight (boundedFlatNormalizedPullbackCompIso m h)
        (boundedFlatNormalizedPullback jb)) := by
  apply Iso.ext
  apply NatTrans.ext
  funext x
  have hx := congrArg (fun e ↦ e.hom.app x) (normalized_square l ja jb m h sq tot)
  simpa only [Iso.trans_hom, NatTrans.comp_app, isoWhiskerLeft_hom,
    whiskerLeft_app, Category.assoc] using hx


/-- Any genuine geometric chart square retains its complete normalization word
in the small model. -/
theorem normalized_small_square {A₀ B₀ A₁ B₁ X : Scheme.{u}}
    (l : B₁ ⟶ B₀) (ja : B₀ ⟶ A₀) (jb : B₁ ⟶ A₁) (m : A₁ ⟶ A₀)
    (h : A₀ ⟶ X) (sq : l ≫ ja = jb ≫ m) (tot : l ≫ ja ≫ h = jb ≫ m ≫ h) :
    smallIso (boundedFlatNormalizedPullbackCompIso l (ja ≫ h)) ≪≫
      smallIso (isoWhiskerRight (boundedFlatNormalizedPullbackCompIso ja h)
        (boundedFlatNormalizedPullback l)) ≪≫
      smallIso (isoWhiskerLeft (boundedFlatNormalizedPullback h)
        ((boundedFlatNormalizedPullbackCompIso l ja).symm ≪≫
        (eqToIso (congrArg boundedFlatNormalizedPullback sq) ≪≫
          boundedFlatNormalizedPullbackCompIso jb m))) =
    smallIso (eqToIso (congrArg boundedFlatNormalizedPullback tot) ≪≫
      boundedFlatNormalizedPullbackCompIso jb (m ≫ h)) ≪≫
      smallIso (isoWhiskerRight (boundedFlatNormalizedPullbackCompIso m h)
        (boundedFlatNormalizedPullback jb)) := by
  exact smallIso_word_three_two _ _ _ _ _
    (normalized_combined_square l ja jb m h sq tot)

variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (f : a ⟶ b)
variable {X : Scheme.{u}} (h : space (op P, (polynomialUnderFunctor R).obj a) ⟶ X)
local notation "l" => coefficientMap P (CategoryTheory.Functor.map (laurentUnderFunctor R) f)
local notation "m" => coefficientMap P (CategoryTheory.Functor.map (polynomialUnderFunctor R) f)
local notation "ja" => laurentPlus P a
local notation "jb" => laurentPlus P b
local notation "N" => boundedFlatNormalizedPullback
local notation "C" => boundedFlatNormalizedPullbackCompIso

/-- The literal coefficient chart square, with its declared geometric endpoint maps. -/
theorem chart_square : l ≫ ja = jb ≫ m :=
  coefficientMap_naturality P (underToLaurent R) f

/-- The actual complete geometric equality keeps the original source reference h. -/
theorem total_square : l ≫ ja ≫ h = jb ≫ m ≫ h :=
  (Category.assoc l ja h).symm.trans
    ((congrArg (fun k ↦ k ≫ h) (chart_square P f)).trans
      (Category.assoc jb m h))

/-- The ordinary anchor is the existing canonical target normalization, not a newly chosen one. -/
theorem ordinary_anchor :
    C l (ja ≫ h) ≪≫ isoWhiskerRight (C ja h) (N l) ≪≫
      isoWhiskerLeft (N h) (C l ja).symm ≪≫
      isoWhiskerLeft (N h)
        (eqToIso (congrArg N (chart_square P f)) ≪≫
          C jb m) =
    eqToIso (congrArg N (total_square P f h)) ≪≫ C jb (m ≫ h) ≪≫
      isoWhiskerRight (C m h) (N jb) :=
  normalized_square l ja jb m h (chart_square P f) (total_square P f h)

open Quillen.Waldhausen.IteratedS BassH0Merge CoefficientBassSeedTargetChartAttachment

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
  normalized_small_square l ja jb m h (chart_square P f) (total_square P f h)

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

/-- The canonical target identification retains the full prescribed forward unit shift. -/
theorem shifted_model_anchor :
    BinaryNormalizationSimplex.total l (ja ≫ h) ≪≫
      targetAnchor P f (normalizedMap h) (normalizedMap (ja ≫ h))
        (Quillen.FunctorIdentityAutomorphism.onFunctor (normalizedMap (ja ≫ h)).functor
          (LaurentUnitReferenceSpecialization.smallUnit P a) ≪≫
            BinaryNormalizationSimplex.total ja h) =
      Quillen.FunctorIdentityAutomorphism.onFunctor (normalizedMap (l ≫ ja ≫ h)).functor
        (LaurentUnitReferenceSpecialization.smallUnit P b) ≪≫
          (canonicalAnchor P f h ≪≫
            isoWhiskerRight (BinaryNormalizationSimplex.total m h) (Jb P (b := b)).functor) := by
  have hs := CoefficientBassSeedTargetUnitReference.shifted_anchor P f
    (normalizedMap (ja ≫ h)) (normalizedMap (l ≫ ja ≫ h))
    (BinaryNormalizationSimplex.total l (ja ≫ h)) (normalizedMap h)
    (BinaryNormalizationSimplex.total ja h)
  exact hs.trans (congrArg
    (fun e ↦ Quillen.FunctorIdentityAutomorphism.onFunctor
      (normalizedMap (l ≫ ja ≫ h)).functor
      (LaurentUnitReferenceSpecialization.smallUnit P b) ≪≫ e)
    (ordinary_model_anchor P f h))

end Quillen.PerfectComplexes.CoefficientBassSeedTargetCanonicalAnchor
