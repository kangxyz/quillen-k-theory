/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.CategoryTheory.QConstruction.Abelian.Cospans

/-! # Composition of ordinary abelian Q-cospans -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory CategoryTheory.Limits
namespace Quillen.Q
attribute [local instance] Abelian.hasFiniteBiproducts
variable {C : Type u} [Category.{v} C] [Abelian C]

@[simp]
theorem surjectionArrow_comp {X Y Z : C} (p : Y ⟶ X) (q : Z ⟶ Y) [Epi p] [Epi q] :
    surjectionArrow p ≫ surjectionArrow q = surjectionArrow (q ≫ p) := by
  let sq : IsPullback q (𝟙 Z) (𝟙 Y) q := IsPullback.of_vert_isIso ⟨by simp⟩
  symm
  apply mkHom_eq_of_apexIso _ _ _ _ sq.isoPullback
  · change sq.isoPullback.hom ≫ pullback.fst (𝟙 Y) q ≫ p = q ≫ p
    simp
  · change sq.isoPullback.hom ≫ pullback.snd (𝟙 Y) q ≫ 𝟙 Z = 𝟙 Z
    simp

@[simp]
theorem inflationArrow_comp {X Y Z : C} (i : X ⟶ Y) (j : Y ⟶ Z) [Mono i] [Mono j] :
    inflationArrow i ≫ inflationArrow j = inflationArrow (i ≫ j) := by
  let sq : IsPullback (𝟙 X) i i (𝟙 Y) := IsPullback.of_horiz_isIso ⟨by simp⟩
  symm
  apply mkHom_eq_of_apexIso _ _ _ _ sq.isoPullback
  · change sq.isoPullback.hom ≫ pullback.fst i (𝟙 Y) ≫ 𝟙 X = 𝟙 X
    simp
  · change sq.isoPullback.hom ≫ pullback.snd i (𝟙 Y) ≫ j = i ≫ j
    simp

@[simp]
theorem inflationArrow_id (X : C) : inflationArrow (𝟙 X) = 𝟙 (of _ _ X) := rfl

@[simp]
theorem surjectionArrow_id (X : C) : surjectionArrow (𝟙 X) = 𝟙 (of _ _ X) := rfl

/-- Reversing an epi does not identify distinct ordinary arrows. -/
theorem surjectionArrow_injective {X Y : C} (p q : Y ⟶ X) [Epi p] [Epi q]
    (h : surjectionArrow p = surjectionArrow q) : p = q := by
  obtain ⟨e, hl, hr⟩ := (mkHom_eq_iff_apexIso _ _ _ _).1 h
  change e.hom ≫ q = p at hl
  change e.hom ≫ 𝟙 Y = 𝟙 Y at hr
  have he : e.hom = 𝟙 Y := by simpa using hr
  rw [he, Category.id_comp] at hl
  exact hl.symm

/-- Mapping a reversed epi agrees with reversing its mapped ordinary arrow. -/
@[simp]
theorem mapQ_surjectionArrow {D : Type u} [Category.{v} D] [Abelian D]
    (F : ExactFunctor (abelianExactStructure C) (abelianExactStructure D))
    {X Y : C} (p : Y ⟶ X) [Epi p] :
    F.mapQ.map (surjectionArrow p) =
      @surjectionArrow D _ _ (F.toFunctor.obj X) (F.toFunctor.obj Y) (F.toFunctor.map p)
        ((abelianExactStructure_deflation_iff D _).1
          (F.toQCompatibleFunctor.map_deflation p ((abelianExactStructure_deflation_iff C p).2
            inferInstance))) := by
  unfold surjectionArrow
  change mkHom _ _ (F.toQCompatibleFunctor.mapSpan _) = mkHom _ _ _
  refine mkHom_eq_of_apexIso _ _ _ _ (Iso.refl (F.toFunctor.obj Y)) ?_ ?_
  · simp [QCompatibleFunctor.mapSpan, ExactFunctor.toQCompatibleFunctor]
  · simp [QCompatibleFunctor.mapSpan, ExactFunctor.toQCompatibleFunctor]

/-- Mapping an ordinary mono agrees with its identity-left-leg Q-arrow. -/
@[simp]
theorem mapQ_inflationArrow {D : Type u} [Category.{v} D] [Abelian D]
    (F : ExactFunctor (abelianExactStructure C) (abelianExactStructure D))
    {X Y : C} (i : X ⟶ Y) [Mono i] :
    F.mapQ.map (inflationArrow i) =
      @inflationArrow D _ _ (F.toFunctor.obj X) (F.toFunctor.obj Y) (F.toFunctor.map i)
        ((abelianExactStructure_inflation_iff D _).1
          (F.toQCompatibleFunctor.map_inflation i ((abelianExactStructure_inflation_iff C i).2
            inferInstance))) := by
  unfold inflationArrow
  change mkHom _ _ (F.toQCompatibleFunctor.mapSpan _) = mkHom _ _ _
  refine mkHom_eq_of_apexIso _ _ _ _ (Iso.refl (F.toFunctor.obj X)) ?_ ?_
  · simp [QCompatibleFunctor.mapSpan, ExactFunctor.toQCompatibleFunctor]
  · simp [QCompatibleFunctor.mapSpan, ExactFunctor.toQCompatibleFunctor]

end Quillen.Q
