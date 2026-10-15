/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Algebra.Homology.DerivedHomVanishing

/-! # Original derived-map consumers for source bounds and cone null-detection -/
@[expose] public section

open Quillen.CochainComplex


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u v w
namespace QuillenTest.DerivedHomVanishing
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
attribute [local instance] Abelian.hasFiniteBiproducts

/-- Every actual derived map in disjoint term supports is uniquely zero. -/
theorem unique_map_between_disjoint_terms (K L : CochainComplex C ℤ) [K.IsKProjective]
    (h : ∀ n, IsZero (K.X n) ∨ IsZero (L.X n)) :
    ∃! _φ : DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj L, True :=
  ⟨0, trivial, fun φ _ => derivedHom_eq_zero_of_disjoint_terms K L h φ⟩

/-- Any two original maps to an arbitrary low single agree, in independent universes. -/
theorem low_single_maps_equal (K : CochainComplex C ℤ) [K.IsKProjective]
    (M : C) (a b : ℤ) (hK : ∀ n, n < b → IsZero (K.X n)) (hab : a < b)
    (φ ψ : DerivedCategory.Q.obj K ⟶
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor C a).obj M)) : φ = ψ :=
  (derivedHom_single_eq_zero_of_lower_terms K M a b hK hab φ).trans
    (derivedHom_single_eq_zero_of_lower_terms K M a b hK hab ψ).symm

/-- Equalities on both actual inclusions determine the entire original derived map
when precisely the shifted-overlap obstruction vanishes. -/
theorem original_cone_maps_equal {T A B : CochainComplex C ℤ} (f : T ⟶ A) (g : T ⟶ B)
    {L : DerivedCategory C}
    (hT : ∀ γ : (DerivedCategory.Q.obj T)⟦(1 : ℤ)⟧ ⟶ L, γ = 0)
    (φ ψ : DerivedCategory.Q.obj (homotopyPushout f g) ⟶ L)
    (hA : DerivedCategory.Q.map (homotopyPushoutInl f g) ≫ φ =
      DerivedCategory.Q.map (homotopyPushoutInl f g) ≫ ψ)
    (hB : DerivedCategory.Q.map (homotopyPushoutInr f g) ≫ φ =
      DerivedCategory.Q.map (homotopyPushoutInr f g) ≫ ψ) : φ = ψ := by
  apply sub_eq_zero.mp
  apply derivedHom_homotopyPushout_eq_zero f g hT (φ - ψ)
  · rw [Preadditive.comp_sub, hA, sub_self]
  · rw [Preadditive.comp_sub, hB, sub_self]

end QuillenTest.DerivedHomVanishing
