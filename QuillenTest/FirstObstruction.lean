/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.LocalCoefficients.FirstObstruction

/-! Degree-two/three, singleton, and disconnected-space first-obstruction tests. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits Quillen.LocalCoefficients
universe u

namespace QuillenTest.FirstObstruction

open Quillen
variable {X : Type u} [TopologicalSpace X]

/-- The degree-two specialization keeps the actual fundamental-group
vanishing hypothesis and genuine integral second homology. -/
theorem degreeTwo [PathConnectedSpace X] (z : X)
    (hπ : ∀ x : X, Subsingleton (HomotopyGroup.Pi 1 X x))
    (hH : IsZero (homology (constant X integralCoefficientModule.{u}) 2)) :
    Subsingleton (HomotopyGroup.Pi 2 X z) := by
  apply subsingleton_pi_of_homology_isZero 0 z ?_ hH
  intro x k hk hlt
  have h : k = 1 := by omega
  subst k
  exact hπ x

/-- Degree three requires both lower positive original homotopy groups. -/
theorem degreeThree [PathConnectedSpace X] (z : X)
    (hπ₁ : ∀ x : X, Subsingleton (HomotopyGroup.Pi 1 X x))
    (hπ₂ : ∀ x : X, Subsingleton (HomotopyGroup.Pi 2 X x))
    (hH : IsZero (homology (constant X integralCoefficientModule.{u}) 3)) :
    Subsingleton (HomotopyGroup.Pi 3 X z) := by
  apply subsingleton_pi_of_homology_isZero 1 z ?_ hH
  intro x k hk hlt
  have h : k = 1 ∨ k = 2 := by omega
  rcases h with rfl | rfl
  · exact hπ₁ x
  · exact hπ₂ x

/-- On an actual singleton subspace, all hypotheses are supplied by the
proved positive point homology calculation and the original loop quotient. -/
theorem singleton_space (z : X) (m : ℕ) :
    Subsingleton (HomotopyGroup.Pi (m + 2) ({z} : Set X) ⟨z, rfl⟩) := by
  let : PathConnectedSpace ({z} : Set X) := {
    nonempty := ⟨⟨z, rfl⟩⟩
    joined := fun a b ↦ by
      have h : a = b := Subsingleton.elim _ _
      subst b
      exact Joined.refl a }
  apply subsingleton_pi_of_homology_isZero (X := ({z} : Set X)) m ⟨z, rfl⟩
  · intro x k _ _
    refine ⟨fun a b ↦ ?_⟩
    refine Quotient.inductionOn₂ a b ?_
    intro p q
    exact congrArg Quotient.mk' (GenLoop.ext p q (fun _ ↦ Subsingleton.elim _ _))
  · exact point_constant_homology_isZero z integralCoefficientModule.{u} (m + 1)

/-- Positive integral homology can vanish in every degree while Pi zero has
more than one element: discrete Bool guards the retained connectivity input. -/
theorem disconnected_bool_guard :
    (∀ n : ℕ, IsZero (homology (constant Bool integralCoefficientModule.{0}) (n + 1))) ∧
      ¬ Subsingleton (HomotopyGroup.Pi 0 Bool false) := by
  constructor
  · intro n
    exact (AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
      (ModuleCat.{0} ℤ) (n + 1) integralCoefficientModule.{0} (TopCat.of Bool)
      (Nat.succ_ne_zero n)).of_iso (constantHomologyIso integralCoefficientModule.{0} (n + 1))
  · intro h
    let := h
    have hz : Subsingleton (ZerothHomotopy Bool) :=
      (HomotopyGroup.pi0EquivZerothHomotopy (X := Bool) (x := false)).symm.injective.subsingleton
    let : PathConnectedSpace Bool :=
      pathConnectedSpace_iff_zerothHomotopy.mpr ⟨⟨ZerothHomotopy.mk false⟩, hz⟩
    let : Subsingleton Bool := subsingleton_of_preconnected_totallyDisconnected
    have hfalse : (false : Bool) = true := Subsingleton.elim _ _
    cases hfalse

/-- The additive theorem's degree parameter cannot silently become degree one. -/
theorem degreeOne_excluded : ¬ ∃ m : ℕ, m + 2 = 1 := by omega

end QuillenTest.FirstObstruction
