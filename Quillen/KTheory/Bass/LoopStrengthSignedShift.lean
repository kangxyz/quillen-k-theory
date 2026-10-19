/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.LoopStrengthInclusion

/-!
# The original target inclusion through two signed shifts

Two inverse original parameter shifts place a Laurent representative in the
second looped cone. Applying the original strength and both forward shifts
recovers the original target inclusion with its actual minus sign. No geometric
factor swap is simplified by this calculation.
-/
@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Quillen.LoopPrespectrum

universe u v w

namespace Quillen.KTheory.Bass.LoopFactor

variable {C : Type u} [Category.{v} C]

private theorem signed_shift_comparison {D : Type*} [Category D] [Preadditive D]
    {A B C E F G H I : D} (s₀ : B ≅ A) (s₁ : C ≅ B) (s₂ : F ≅ E)
    (s₃ : H ≅ G) (s₄ : G ≅ I) (l : B ⟶ E) (lΩ : C ⟶ F) (k : F ⟶ H)
    (jΩΩ : C ⟶ H) (jΩ : B ⟶ G) (j : A ⟶ I)
    (h₁ : s₁.inv ≫ lΩ = l ≫ s₂.inv) (h₂ : lΩ ≫ k = -jΩΩ)
    (h₃ : jΩΩ ≫ s₃.hom = s₁.hom ≫ jΩ) (h₄ : jΩ ≫ s₄.hom = s₀.hom ≫ j) :
    s₀.inv ≫ l ≫ s₂.inv ≫ k ≫ s₃.hom ≫ s₄.hom = -j := by
  rw [← Category.assoc l, ← h₁]
  simp only [Category.assoc]
  rw [← Category.assoc lΩ, h₂]
  simp only [Preadditive.neg_comp, Preadditive.comp_neg]
  apply congrArg Neg.neg
  rw [← Category.assoc jΩΩ, h₃]
  simp only [Category.assoc]
  rw [Iso.inv_hom_id_assoc, h₄, Iso.inv_hom_id_assoc]

/-- The original two signed shifts retain the transpose sign on every Laurent representative. -/
theorem strength_inclusion_signedShift (Q : C ⥤ Arrow (Arrow C))
    (F : C ⥤ LoopPrespectrum.{w}) (X : C) (d : ℤ) :
    let S := F.mapArrow.mapArrow.obj (Q.obj X)
    (parameterStableHomotopyIso S.right.right (d + 1)).inv ≫
      (stableHomotopyFunctor (d + 1)).map
        (mappingConeInclusion (StrictSquare.comparison (loopSquare S))) ≫
      (parameterStableHomotopyIso (mappingCone (StrictSquare.comparison (loopSquare S))) d).inv ≫
      (stableHomotopyFunctor d).map (LoopStrength.strength Q F X) ≫
      (parameterStableHomotopyIso
        (parameterLooping (mappingCone (StrictSquare.comparison S))) d).hom ≫
      (parameterStableHomotopyIso (mappingCone (StrictSquare.comparison S)) (d + 1)).hom =
    -((stableHomotopyFunctor ((d + 1) + 1)).map
      (mappingConeInclusion (StrictSquare.comparison S))) := by
  dsimp only
  let S := F.mapArrow.mapArrow.obj (Q.obj X)
  let j := mappingConeInclusion (StrictSquare.comparison S)
  let jl := mappingConeInclusion (StrictSquare.comparison (loopSquare S))
  have h₁ := parameterStableHomotopyIso_inv_naturality jl d
  have h₂ := strength_inclusion_stable Q F X d
  have h₃ := parameterStableHomotopyIso_naturality (parameterLoopingMap j) d
  have h₄ := parameterStableHomotopyIso_naturality j (d + 1)
  exact signed_shift_comparison
    (parameterStableHomotopyIso S.right.right (d + 1))
    (parameterStableHomotopyIso (parameterLooping S.right.right) d)
    (parameterStableHomotopyIso (mappingCone (StrictSquare.comparison (loopSquare S))) d)
    (parameterStableHomotopyIso (parameterLooping (mappingCone (StrictSquare.comparison S))) d)
    (parameterStableHomotopyIso (mappingCone (StrictSquare.comparison S)) (d + 1))
    _ _ _ _ _ _ h₁ h₂ h₃ h₄

end Quillen.KTheory.Bass.LoopFactor
