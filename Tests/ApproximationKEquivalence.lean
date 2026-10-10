/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Waldhausen.Approximation.KEquivalence

/-! Behavioral consumers of approximation for the unchanged S/K maps. -/
@[expose] public section

noncomputable section
open CategoryTheory
universe u
namespace ApproximationKConsumers
open Quillen Quillen.Waldhausen
variable {C D E : Type u} [SmallCategory C] [SmallCategory D] [SmallCategory E]
  {W : Structure C} {V : Structure D} {U : Structure E} {F : C ⥤ D} {G : D ⥤ E}
  (h : HasApproximationProperty W V F)
  (hF : IsExact W.cof W.weq V.cof V.weq F)
  [V.weq.HasTwoOutOfThreeProperty]
  (J : Fibration.RowFactorization.JointData (Fibration.NestedWeakEquivalences.refl W))

include h J in
/-- Every actual target S-realization point is joined to the image of an original source point. -/
theorem original_delooping_component (y : V.Delooping) :
    ∃ x, Joined (deloopingMap hF x) y :=
  (h.deloopingMap_isWeakHomotopyEquivalence hF J).component_surjective y

include h J in
/-- All-degree bijectivity uses the literal induced homotopy map at every original source point. -/
theorem original_delooping_homotopy_map (x : W.Delooping) (n : ℕ) :
    Function.Bijective (homotopyGroupMap (N := Fin n) (deloopingMap hF).hom (x := x) rfl) :=
  (h.deloopingMap_isWeakHomotopyEquivalence hF J).homotopy_bijective x n

/-- The constructed inverse really is a right inverse for the canonical original K-zero map. -/
theorem original_K_zero_right_inverse (a : V.K 0) :
    KMap hF 0 ((h.KEquiv hF J 0).symm a) = a :=
  (h.KEquiv hF J 0).apply_symm_apply a

/-- In every degree it is also a left inverse for the unchanged canonical K-map. -/
theorem original_K_left_inverse (n : ℕ) (a : W.K n) :
    (h.KEquiv hF J n).symm (KMap hF n a) = a :=
  (h.KEquiv hF J n).symm_apply_apply a

/-- Composing approximation equivalences retains the original exact-composite K-map,
including its canonical chosen-zero normalization. -/
theorem original_K_composite
    (hG : IsExact V.cof V.weq U.cof U.weq G)
    (h' : HasApproximationProperty V U G) [U.weq.HasTwoOutOfThreeProperty]
    (J' : Fibration.RowFactorization.JointData (Fibration.NestedWeakEquivalences.refl V))
    (n : ℕ) :
    ((h.KEquiv hF J n).trans (h'.KEquiv hG J' n)).toMonoidHom = KMap (hF.comp hG) n := by
  rw [← KMap_comp_KMap]
  rfl

end ApproximationKConsumers
