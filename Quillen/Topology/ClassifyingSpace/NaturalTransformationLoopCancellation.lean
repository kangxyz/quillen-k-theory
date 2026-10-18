/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.CategoryTheory.TheoremB.NaturalTransformationCancellation
public import Quillen.Topology.Homotopy.ConcatenationFamilies

/-!
# Whole-source cancellation of original natural-transformation loop families

The original composition triangle, path reversal and associator give a jointly
continuous endpoint-relative homotopy over the entire source classifying space.
The source vertex may have a nonconstant track. No fiber-boundary or Serre law
is an input. The current consumer is the original Q-diagram cap calibration.
-/
@[expose] public noncomputable section

universe u v
open CategoryTheory
open scoped Topology unitInterval

namespace Quillen

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  {f₀ f₁ f₂ : C(X, Y)}

/-- Reverse the path coordinate of an entire endpoint-relative homotopy family. -/
def homotopyRelReversePaths {H K : f₀.Homotopy f₁}
    (J : H.toContinuousMap.HomotopyRel K.toContinuousMap
      {z : unitInterval × X | z.1 = 0 ∨ z.1 = 1}) :
    H.symm.toContinuousMap.HomotopyRel K.symm.toContinuousMap
      {z : unitInterval × X | z.1 = 0 ∨ z.1 = 1} where
  toFun z := J (z.1, (unitInterval.symm z.2.1, z.2.2))
  continuous_toFun := by fun_prop
  map_zero_left z := J.apply_zero (unitInterval.symm z.1, z.2)
  map_one_left z := J.apply_one (unitInterval.symm z.1, z.2)
  prop' s z hz := by
    apply J.prop s (unitInterval.symm z.1, z.2)
    rcases hz with h | h
    · right
      simp only [h, unitInterval.symm_zero]
    · left
      simp only [h, unitInterval.symm_one]

/-- Prepend the same original path family throughout a whole relative homotopy. -/
def homotopyRelPrependPaths (L : f₀.Homotopy f₁) {H K : f₁.Homotopy f₂}
    (J : H.toContinuousMap.HomotopyRel K.toContinuousMap
      {z : unitInterval × X | z.1 = 0 ∨ z.1 = 1}) :
    (L.trans H).toContinuousMap.HomotopyRel (L.trans K).toContinuousMap
      {z : unitInterval × X | z.1 = 0 ∨ z.1 = 1} := by
  let p : C(unitInterval × X, X) := ContinuousMap.snd
  let V : (f₁.comp p).Homotopy (f₂.comp p) := {
    toFun z := J (z.2.1, (z.1, z.2.2))
    continuous_toFun := by fun_prop
    map_zero_left z := (J.prop z.1 (0, z.2) (Or.inl rfl)).trans (H.apply_zero z.2)
    map_one_left z := (J.prop z.1 (1, z.2) (Or.inr rfl)).trans (H.apply_one z.2) }
  let W := (L.compContinuousMap p).trans V
  exact {
    toFun z := W (z.2.1, (z.1, z.2.2))
    continuous_toFun := by fun_prop
    map_zero_left z := by
      change ((L.compContinuousMap p).trans V) (z.1, (0, z.2)) = (L.trans H) z
      rw [ContinuousMap.Homotopy.trans_apply, ContinuousMap.Homotopy.trans_apply]
      split_ifs
      · rfl
      · exact J.apply_zero _
    map_one_left z := by
      change ((L.compContinuousMap p).trans V) (z.1, (1, z.2)) = (L.trans K) z
      rw [ContinuousMap.Homotopy.trans_apply, ContinuousMap.Homotopy.trans_apply]
      split_ifs
      · rfl
      · exact J.apply_one _
    prop' s z hz := by
      obtain ⟨t, x⟩ := z
      rcases hz with h | h
      · change t = 0 at h
        subst t
        change W (0, (s, x)) = (L.trans H) (0, x)
        rw [W.apply_zero, ContinuousMap.Homotopy.apply_zero]
        rfl
      · change t = 1 at h
        subst t
        change W (1, (s, x)) = (L.trans H) (1, x)
        rw [W.apply_one, ContinuousMap.Homotopy.apply_one]
        rfl }

end Quillen

namespace Quillen.TheoremB

variable {A B : Type u} [SmallCategory A] [SmallCategory B]
  {P₀ P₁ P₂ : A ⥤ B} (α : P₀ ⟶ P₁) (β γ : P₁ ⟶ P₂)

/-- Cancel the original first transformation inside the displayed loop family, jointly over
all source points and relative to both path-time endpoints. -/
def naturalTransformationLoopCancellationHomotopy :
    (((classifyingSpaceNaturalTransformationHomotopy (α ≫ β)).trans
      (classifyingSpaceNaturalTransformationHomotopy γ).symm).symm.trans
        (classifyingSpaceNaturalTransformationHomotopy α)).toContinuousMap.HomotopyRel
      ((classifyingSpaceNaturalTransformationHomotopy γ).trans
        (classifyingSpaceNaturalTransformationHomotopy β).symm).toContinuousMap
      {z : unitInterval × ClassifyingSpace A | z.1 = 0 ∨ z.1 = 1} := by
  let J := homotopyRelReversePaths (naturalTransformationCancellationHomotopy α β)
  have J' :
      ((classifyingSpaceNaturalTransformationHomotopy (α ≫ β)).symm.trans
        (classifyingSpaceNaturalTransformationHomotopy α)).toContinuousMap.HomotopyRel
      (classifyingSpaceNaturalTransformationHomotopy β).symm.toContinuousMap
      {z : unitInterval × ClassifyingSpace A | z.1 = 0 ∨ z.1 = 1} := by
    simpa only [ContinuousMap.Homotopy.symm_trans, ContinuousMap.Homotopy.symm_symm] using J
  simpa only [ContinuousMap.Homotopy.symm_trans, ContinuousMap.Homotopy.symm_symm] using
    (homotopyAssociator (classifyingSpaceNaturalTransformationHomotopy γ)
      (classifyingSpaceNaturalTransformationHomotopy (α ≫ β)).symm
      (classifyingSpaceNaturalTransformationHomotopy α)).trans
        (homotopyRelPrependPaths (classifyingSpaceNaturalTransformationHomotopy γ) J')

/-- Every new homotopy time fixes the original first endpoint at the P₁-map. -/
theorem naturalTransformationLoopCancellationHomotopy_zero
    (s : unitInterval) (x : ClassifyingSpace A) :
    naturalTransformationLoopCancellationHomotopy α β γ (s, (0, x)) =
      classifyingSpaceMap P₁ x :=
  ((naturalTransformationLoopCancellationHomotopy α β γ).prop s (0, x) (Or.inl rfl)).trans
    (ContinuousMap.Homotopy.apply_zero _ x)

/-- Every new homotopy time fixes the original last endpoint at the P₁-map. -/
theorem naturalTransformationLoopCancellationHomotopy_one
    (s : unitInterval) (x : ClassifyingSpace A) :
    naturalTransformationLoopCancellationHomotopy α β γ (s, (1, x)) =
      classifyingSpaceMap P₁ x :=
  ((naturalTransformationLoopCancellationHomotopy α β γ).prop s (1, x) (Or.inr rfl)).trans
    (ContinuousMap.Homotopy.apply_one _ x)

end Quillen.TheoremB
