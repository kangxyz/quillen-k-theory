/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
import Quillen.Waldhausen.Approximation.ReedyFactorization

/-!
# Coherent replacement of original square diagrams by Reedy squares

The given original functorial factorization replaces arbitrary arrows by
cofibrations. Applying this to an entire original square, then using the proved
Reedy-arrow factorization, yields an actual Reedy square with a natural,
componentwise weak comparison to the original square. The initial vertex is
retained literally. No original arrows are assumed to be cofibrations.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe v u

namespace Quillen.Waldhausen.FunctorialFactorization
variable {C : Type u} [Category.{v} C] {W : Structure C}
  (T : FunctorialFactorization W)

/-- An arbitrary original arrow is replaced by its genuine cofibration factor,
naturally on every original square. -/
def cofibrationArrowReplacement : Arrow C ⥤ ExtensionCategory.Obj W :=
  (ExtensionCategory.objects W).lift
    (ArrowDiagrams.toDiagramObj (Arrow.mk T.inclusion)) T.cofibration

/-- The replacement comparison uses the identity at the original source and
the original weak projection at the target. -/
def cofibrationArrowProjection :
    T.cofibrationArrowReplacement ⋙ ExtensionCategory.forget W ⟶ 𝟭 (Arrow C) where
  app f := Arrow.homMk (𝟙 f.left) (T.projection.app f) (by
    change (𝟙 f.left) ≫ f.hom = T.inclusion.app f ≫ T.projection.app f
    rw [Category.id_comp, T.factorization])
  naturality f g φ := by
    apply Arrow.hom_ext
    · change φ.left ≫ (𝟙 g.left) = (𝟙 f.left) ≫ φ.left
      simp
    · exact T.projection.naturality φ

/-- Both actual projection components are weak equivalences. -/
theorem cofibrationArrowProjection_weak (f : Arrow C) :
    W.weq (T.cofibrationArrowProjection.app f).left ∧
      W.weq (T.cofibrationArrowProjection.app f).right :=
  ⟨W.weq.id_mem _, T.weak _⟩

/-- The original source vertex is retained literally. -/
@[simp] theorem cofibrationArrowReplacement_source (f : Arrow C) :
    (T.cofibrationArrowReplacement.obj f).obj.left = f.left := rfl

/-- The projection at the original source is literally its identity. -/
@[simp] theorem cofibrationArrowProjection_source (f : Arrow C) :
    (T.cofibrationArrowProjection.app f).left = 𝟙 f.left := rfl

/-- Under the actual saturation axiom, replacement preserves pointwise weak
squares because its comparison is already natural and pointwise weak. -/
theorem cofibrationArrowReplacement_weak [W.weq.HasTwoOutOfThreeProperty]
    {f g : Arrow C} (φ : f ⟶ g) (hl : W.weq φ.left) (hr : W.weq φ.right) :
    ExtensionCategory.weq W (T.cofibrationArrowReplacement.map φ) := by
  refine ⟨hl, ?_⟩
  apply W.weq.of_postcomp _ (T.projection.app g) (T.weak g)
  change W.weq (T.middle.map φ ≫ T.projection.app g)
  rw [T.projection.naturality]
  exact W.weq.comp_mem _ _ (T.weak f) hr

/-- Forget a genuine Reedy square to its original iterated-arrow diagram. -/
def reedySquareForget :
    ExtensionCategory.Obj (ExtensionCategory.waldhausenStructure W) ⥤ Arrow (Arrow C) :=
  ExtensionCategory.forget (ExtensionCategory.waldhausenStructure W) ⋙
    (ExtensionCategory.forget W).mapArrow

/-- Every arbitrary original commutative square admits a genuine, functorial
Reedy replacement; there is no cofibration assumption on the input. -/
def reedySquareReplacement :
    Arrow (Arrow C) ⥤ ExtensionCategory.Obj (ExtensionCategory.waldhausenStructure W) :=
  T.cofibrationArrowReplacement.mapArrow ⋙ T.reedyFactorization.cofibrationArrowReplacement

/-- The two successive original comparisons give a strictly natural comparison
from the actual Reedy replacement to the original square. -/
def reedySquareProjection :
    T.reedySquareReplacement ⋙ reedySquareForget (W := W) ⟶ 𝟭 (Arrow (Arrow C)) :=
  Functor.whiskerRight
      (Functor.whiskerLeft T.cofibrationArrowReplacement.mapArrow
        T.reedyFactorization.cofibrationArrowProjection)
      (ExtensionCategory.forget W).mapArrow ≫
    (Functor.mapArrowFunctor (Arrow C) (Arrow C)).map T.cofibrationArrowProjection

/-- All four projection components are genuine weak equivalences. -/
theorem reedySquareProjection_weak (f : Arrow (Arrow C)) :
    W.weq (T.reedySquareProjection.app f).left.left ∧
    W.weq (T.reedySquareProjection.app f).left.right ∧
    W.weq (T.reedySquareProjection.app f).right.left ∧
    W.weq (T.reedySquareProjection.app f).right.right := by
  let q := T.reedyFactorization.cofibrationArrowProjection.app
    (T.cofibrationArrowReplacement.mapArrow.obj f)
  have hq := T.reedyFactorization.cofibrationArrowProjection_weak
    (T.cofibrationArrowReplacement.mapArrow.obj f)
  have hl := T.cofibrationArrowProjection_weak f.left
  have hr := T.cofibrationArrowProjection_weak f.right
  exact ⟨W.weq.comp_mem _ _ hq.1.1 hl.1,
    W.weq.comp_mem _ _ hq.1.2 hl.2,
    W.weq.comp_mem _ _ hq.2.1 hr.1,
    W.weq.comp_mem _ _ hq.2.2 hr.2⟩

/-- The minimal vertex of an arbitrary original square is unchanged. -/
@[simp] theorem reedySquareReplacement_initial (f : Arrow (Arrow C)) :
    (T.reedySquareReplacement.obj f).obj.left.obj.left = f.left.left := rfl

/-- The actual comparison at the retained minimal vertex is identity. -/
@[simp] theorem reedySquareProjection_initial (f : Arrow (Arrow C)) :
    (T.reedySquareProjection.app f).left.left = 𝟙 f.left.left := by
  change (𝟙 f.left.left) ≫ (𝟙 f.left.left) = 𝟙 f.left.left
  simp

end Quillen.Waldhausen.FunctorialFactorization
