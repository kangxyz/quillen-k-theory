/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.SelfBaseChangeModel

/-!
# The actual exact flasque self-base-change weak span

The span is T_P(p* p_* M) → T_P(p2_* T_Z(p1* M)) ← p2_* T_Z(p1* M).
The first arrow is literal total of the proved original alpha. The second is
the original forward Godement augmentation. Every arrow is natural and weak;
all three functors are exact in the actual original flasque Waldhausen model.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Quillen.SchemeSheaf Quillen.Scheme.ProjectiveLine
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.PerfectComplexes.ProjectiveLine.SelfBaseChange
variable (R : CommRingCat.{u})

/-- The actual original alpha lifted to the full bounded-below perfect model. -/
def alpha : source R ⟶ target R ⋙ FlasqueBoundedBelow.inclusion (twoChartLine R) where
  app K := ObjectProperty.homMk ((alphaPlus R).app K).hom
  naturality {K L} s := by
    apply ObjectProperty.hom_ext
    have hn := alphaPlus_naturality_hom R s
    rw [sourcePlus_map_hom, targetPlus_map_hom] at hn
    exact hn

/-- The original alpha is genuinely weak, by the original derived-mate proof. -/
lemma alpha_weak (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    (BoundedBelow.waldhausen (twoChartLine R)).weq ((alpha R).app K) :=
  alphaPlus_quasiIso R K

/-- The first endpoint is literal total of p* p_* M. -/
def spanLeft : FlasqueBoundedBelow.Obj (twoChartLine R) ⥤
    FlasqueBoundedBelow.Obj (twoChartLine R) :=
  source R ⋙ FlasqueBoundedBelow.total (twoChartLine R)

/-- The center endpoint is literal total of the actual second-projection target. -/
def spanCenter : FlasqueBoundedBelow.Obj (twoChartLine R) ⥤
    FlasqueBoundedBelow.Obj (twoChartLine R) :=
  (target R ⋙ FlasqueBoundedBelow.inclusion (twoChartLine R)) ⋙
    FlasqueBoundedBelow.total (twoChartLine R)

/-- The full-model alpha retains the original Plus chain-map data before totalization. -/
lemma alpha_hom_app (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    ((alpha R).app K).hom = ((alphaPlus R).app K).hom := rfl

/-- The left arrow is literal total of the actual original full-model alpha. -/
def spanLeftMap : spanLeft R ⟶ spanCenter R :=
  CategoryTheory.Functor.whiskerRight (alpha R)
    (FlasqueBoundedBelow.total (twoChartLine R))

/-- The right arrow retains the actual forward unit on the actual target. -/
def spanRightMap : target R ⟶ spanCenter R where
  app K := ObjectProperty.homMk
    ((godementTotalUnit (twoChartLine R)).app ((targetRaw R).obj K))
  naturality {K L} s := by
    apply ObjectProperty.hom_ext
    exact (godementTotalUnit (twoChartLine R)).naturality ((targetRaw R).map s)

lemma spanLeftMap_hom_app (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    ((spanLeftMap R).app K).hom =
      (godementTotal (twoChartLine R)).map ((alpha R).app K).hom := rfl

lemma spanRightMap_hom_app (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    ((spanRightMap R).app K).hom =
      (godementTotalUnit (twoChartLine R)).app ((targetRaw R).obj K) := rfl

/-- The span compares the actual alpha through the original augmentation square. -/
lemma span_original_augmentation_square (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    (godementTotalUnit (twoChartLine R)).app ((source R).obj K).obj ≫
        ((spanLeftMap R).app K).hom =
      ((alpha R).app K).hom ≫ ((spanRightMap R).app K).hom :=
  ((godementTotalUnit (twoChartLine R)).naturality ((alpha R).app K).hom).symm

/-- Both weak-arrow proofs apply to the actual chain maps. -/
lemma spanLeftMap_weak (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq ((spanLeftMap R).app K) :=
  FlasqueBoundedBelow.total_weak ((alpha R).app K) (alpha_weak R K)

lemma spanRightMap_weak (K : FlasqueBoundedBelow.Obj (twoChartLine R)) :
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq ((spanRightMap R).app K) :=
  FlasqueBoundedBelow.flasqueUnit_weak (twoChartLine R) ((target R).obj K)

/-- All three original functors are genuinely Waldhausen-exact. -/
lemma spanLeft_exact : Waldhausen.IsExact
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).cof
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).cof
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq (spanLeft R) :=
  (source_exact R).comp (FlasqueBoundedBelow.total_exact (twoChartLine R))

lemma spanCenter_exact : Waldhausen.IsExact
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).cof
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).cof
    (FlasqueBoundedBelow.waldhausen (twoChartLine R)).weq (spanCenter R) :=
  ((target_exact R).comp (FlasqueBoundedBelow.inclusion_exact (twoChartLine R))).comp
    (FlasqueBoundedBelow.total_exact (twoChartLine R))

/-- The endpoints retain the same original strict lower bound. -/
lemma spanLeft_isStrictlyGE (K : FlasqueBoundedBelow.Obj (twoChartLine R))
    (a : ℤ) [K.obj.IsStrictlyGE a] : ((spanLeft R).obj K).obj.IsStrictlyGE a := by
  let := source_isStrictlyGE R K a
  exact FlasqueBoundedBelow.total_isStrictlyGE (twoChartLine R) ((source R).obj K) a

lemma spanCenter_isStrictlyGE (K : FlasqueBoundedBelow.Obj (twoChartLine R))
    (a : ℤ) [K.obj.IsStrictlyGE a] : ((spanCenter R).obj K).obj.IsStrictlyGE a := by
  have : ((FlasqueBoundedBelow.inclusion (twoChartLine R)).obj
      ((target R).obj K)).obj.IsStrictlyGE a := targetRaw_isStrictlyGE R K a
  exact FlasqueBoundedBelow.total_isStrictlyGE (twoChartLine R)
    ((FlasqueBoundedBelow.inclusion (twoChartLine R)).obj ((target R).obj K)) a

/-- Naturality is expressed in the original full model with all original chain maps. -/
@[reassoc]
lemma spanLeftMap_naturality {K L : FlasqueBoundedBelow.Obj (twoChartLine R)} (s : K ⟶ L) :
    (spanLeft R).map s ≫ (spanLeftMap R).app L =
      (spanLeftMap R).app K ≫ (spanCenter R).map s := (spanLeftMap R).naturality s

@[reassoc]
lemma spanRightMap_naturality {K L : FlasqueBoundedBelow.Obj (twoChartLine R)} (s : K ⟶ L) :
    (target R).map s ≫ (spanRightMap R).app L =
      (spanRightMap R).app K ≫ (spanCenter R).map s := (spanRightMap R).naturality s

/-- Actual zero objects are preserved, hence the installed chosen-zero rebasing applies. -/
lemma span_zero {K : FlasqueBoundedBelow.Obj (twoChartLine R)} (hK : IsZero K) :
    IsZero ((spanLeft R).obj K) ∧ IsZero ((spanCenter R).obj K) ∧
      IsZero ((target R).obj K) :=
  ⟨(spanLeft_exact R).zero hK, (spanCenter_exact R).zero hK, (target_exact R).zero hK⟩

end Quillen.PerfectComplexes.ProjectiveLine.SelfBaseChange
