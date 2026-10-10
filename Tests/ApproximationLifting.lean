/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Waldhausen.Approximation.RelativeFlags
public import Quillen.Waldhausen.Approximation.WeakComma

/-! # Consumers of actual cross-category approximation lifting

These checks use arbitrary source and target object/hom universes. The strongest
consumer derives App2 from strict categorical fullness and essential surjectivity,
weak reflection, and an actual source factorization, then factors an arbitrary
map of finite flags while retaining the source zero.
-/
@[expose] public section


noncomputable section

open CategoryTheory CategoryTheory.Limits Quillen.Waldhausen

universe v u v' u'

namespace Quillen.Tests.ApproximationLifting

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {W : Structure C} {V : Structure D} {F : C ⥤ D}
  (hF : IsExact W.cof W.weq V.cof V.weq F)

theorem fullEssSurj_finiteFlag_factorization [F.Full] [F.EssSurj] (T : FunctorialFactorization W)
    (hreflect : ∀ {X Y : C} (f : X ⟶ Y), V.weq (F.map f) → W.weq f)
    (n : ℕ) (A : WeakFlag W.cof W.weq n) (B : WeakFlag V.cof V.weq n)
    (α : A.diagram ⋙ F ⟶ B.diagram) :
    ∃ (A' : WeakFlag W.cof W.weq n) (i : A.diagram ⟶ A'.diagram)
      (p : (hF.weakFlagFunctor n).obj A' ⟶ B),
      (∀ k, W.cof (i.app k)) ∧
        Functor.whiskerRight i F ≫ p.val = α ∧ A'.diagram.obj 0 = A.diagram.obj 0 :=
  (HasApproximationProperty.of_full_essSurj T hF.weak hreflect).exists_relativeFlag hF A B α

theorem fullEssSurj_flagComma_nonempty [F.Full] [F.EssSurj] (T : FunctorialFactorization W)
    (hreflect : ∀ {X Y : C} (f : X ⟶ Y), V.weq (F.map f) → W.weq f)
    (n : ℕ) (B : WeakFlag V.cof V.weq n) :
    Nonempty (CostructuredArrow (hF.weakFlagFunctor n) B) :=
  (HasApproximationProperty.of_full_essSurj T hF.weak hreflect).flagComma_nonempty hF n B

theorem weakComma_has_common_successor [V.weq.HasTwoOutOfThreeProperty]
    (h : HasApproximationProperty W V F) (Y : WideSubcategory V.weq)
    (A B : HasApproximationProperty.WeakComma hF Y) :
    ∃ (Z : HasApproximationProperty.WeakComma hF Y) (a : A ⟶ Z) (b : B ⟶ Z),
      W.cof a.left.hom ∧ W.cof b.left.hom :=
  ⟨h.weakCommaPairTarget hF Y A B,
    h.weakCommaPairLeft hF Y A B, h.weakCommaPairRight hF Y A B,
    h.weakCommaPairLeft_cof hF Y A B, h.weakCommaPairRight_cof hF Y A B⟩

theorem relativeFlag_weak_cofibration [V.weq.HasTwoOutOfThreeProperty]
    (h : HasApproximationProperty W V F) (n : ℕ)
    (A : WeakFlag W.cof W.weq n) (B : WeakFlag V.cof V.weq n)
    (α : (hF.weakFlagFunctor n).obj A ⟶ B) (k : Fin (n + 1)) :
    W.cof ((h.relativeFlagInclusion hF A B α.val).app k) ∧
      W.weq ((h.relativeFlagInclusion hF A B α.val).app k) :=
  ⟨h.relativeFlagInclusion_cof hF A B α.val k,
    h.relativeFlagInclusion_weak hF A B α.val α.property k⟩

theorem finiteLift_retains_initial_data (h : HasApproximationProperty W V F) (n : ℕ)
    (G : ComposableArrows D n) {X : C} (p : F.obj X ⟶ G.obj 0) :
    (h.finiteLift n G p).obj 0 = X ∧ (h.finiteComparison n G p).app 0 = p :=
  ⟨rfl, h.finiteComparison_app_zero n G p⟩

include hF in
/-- The constructed square has both genuine source cofibrations and all three
original strict commutative faces. The proof uses no assumed square lift. -/
theorem relative_square_cofibrations_and_strict_faces
    (h : HasApproximationProperty W V F)
    {A B A' : C} {Y Z : D} (a : A ⟶ B) (i : A ⟶ A')
    (p : F.obj A' ⟶ Y) (b : Y ⟶ Z) (q : F.obj B ⟶ Z)
    (ha : W.cof a) (hi : W.cof i)
    (comm : F.map a ≫ q = F.map i ≫ p ≫ b) :
    ∃ (R : C) (j : B ⟶ R) (k : A' ⟶ R) (r : F.obj R ⟶ Z),
      W.cof j ∧ W.cof k ∧ V.weq r ∧
        a ≫ j = i ≫ k ∧ F.map j ≫ r = q ∧ F.map k ≫ r = p ≫ b := by
  let s := h.squareLift hF a i p b q ha hi comm
  exact ⟨s.obj, s.fromSource, s.fromLift, s.projection, s.fromSource_cof,
    s.fromLift_cof, s.projection_weak, s.square, s.source_projection, s.lift_projection⟩

/-- Weak reflection is used at every lifted arrow, not just on objects. -/
theorem sequenceLift_weak_cofibration [V.weq.HasTwoOutOfThreeProperty]
    (h : HasApproximationProperty W V F) (G : ℕ ⥤ D)
    {X : C} (p : F.obj X ⟶ G.obj 0) (hp : V.weq p)
    {i j : ℕ} (f : i ⟶ j) (hf : V.weq (G.map f)) :
    W.cof ((h.sequenceLift G p).map f) ∧ W.weq ((h.sequenceLift G p).map f) :=
  ⟨h.sequenceLift_map_cof G p f, h.sequenceLift_map_weak G p hp f hf⟩

/-- The induced weak functor preserves the literal original morphism. -/
theorem weakFunctor_retains_map {X Y : WideSubcategory W.weq} (f : X ⟶ Y) :
    (hF.weakFunctor.map f).hom = F.map f.hom := rfl

/-- Nonempty and connected is the exact proved endpoint, with target
saturation explicit and no contractibility or cylinder hypothesis. -/
theorem connected_weakComma [V.weq.HasTwoOutOfThreeProperty]
    (h : HasApproximationProperty W V F) (Y : WideSubcategory V.weq) :
    IsConnected (HasApproximationProperty.WeakComma hF Y) :=
  h.weakComma_connected hF Y

/-- Relative replacement preserves both actual zero maps, not only its object. -/
theorem relativeFlag_retains_zero_maps (h : HasApproximationProperty W V F)
    (n : ℕ) (A : WeakFlag W.cof W.weq n) (B : WeakFlag V.cof V.weq n)
    (α : A.diagram ⋙ F ⟶ B.diagram) :
    (h.relativeFlagInclusion hF A B α).app 0 = 𝟙 (A.diagram.obj 0) ∧
      (h.relativeFlagProjection hF A B α).app 0 = α.app 0 :=
  ⟨h.relativeFlagInclusion_app_zero hF A B α, h.relativeFlagProjection_app_zero hF A B α⟩

end Quillen.Tests.ApproximationLifting
