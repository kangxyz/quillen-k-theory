/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.KTheory.Plus.ProjectiveGroupCompletion
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.ZMod.Basic

/-! # Finite projective module regression tests

The exact structure and complementary summands work for arbitrary rings,
right modules through the opposite ring, a noncommutative matrix ring, and
the zero ring. No invariant-basis-number assumption is present.
-/
@[expose] public section

noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits
open Quillen.FiniteProjectiveModule

example (R : Type u) [Ring R]
    (S : ShortComplex (Quillen.FiniteProjectiveModule.Category.{u, v} R))
    (hS : (exactStructure R).conflation S) : S.Splitting :=
  splittingOfConflation R S hS

example (R : Type u) [Ring R]
    (S : ShortComplex (Quillen.FiniteProjectiveModule.Category.{u, v} Rᵐᵒᵖ)) :
    (exactStructure Rᵐᵒᵖ).conflation S ↔ Nonempty S.Splitting :=
  conflation_iff_nonempty_splitting Rᵐᵒᵖ S

example (R : Type u) [Ring R] (M : Quillen.FiniteProjectiveModule.Category.{u, u} Rᵐᵒᵖ) :
    ∃ (n : ℕ) (Q : ModuleCat.{u} Rᵐᵒᵖ),
      Module.Finite Rᵐᵒᵖ Q ∧ Module.Projective Rᵐᵒᵖ Q ∧
      Nonempty ((M.obj × Q) ≃ₗ[Rᵐᵒᵖ] (Fin n → Rᵐᵒᵖ)) :=
  exists_complement_equiv_fin M.obj

example : Quillen.ExactStructure
    (Quillen.FiniteProjectiveModule.Category (Matrix (Fin 2) (Fin 2) ℤ)) :=
  exactStructure _

example : Quillen.ExactStructure (Quillen.FiniteProjectiveModule.Category (ZMod 1)) :=
  exactStructure _

example : ∃ (n : ℕ) (Q : ModuleCat.{0} (ZMod 1)),
    Module.Finite (ZMod 1) Q ∧ Module.Projective (ZMod 1) Q ∧
    Nonempty (((ModuleCat.of (ZMod 1) (ZMod 1)) × Q) ≃ₗ[ZMod 1] (Fin n → ZMod 1)) :=
  exists_complement_equiv_fin _

section DirectSum

open MonoidalCategory
attribute [local instance] categoryDirectSumMonoidal categoryDirectSumSymmetric
  directSumMonoidal directSumSymmetric

example (R : Type u) [Ring R] : SymmetricCategory (IsoCategory R) := inferInstance

example (R : Type u) [Ring R] (P : IsoCategory Rᵐᵒᵖ) :
    ∃ (n : ℕ) (Q : IsoCategory Rᵐᵒᵖ),
      Nonempty (P ⊗ Q ≅ rankOnePower Rᵐᵒᵖ n) :=
  rankOne_cofinal Rᵐᵒᵖ P

example (R : Type u) [Ring R] (P : IsoCategory R) : (tensorLeft P).Faithful :=
  directSumLeft_faithful R P

example (R : Type u) [Ring R] (P : IsoCategory R) : (tensorRight P).Faithful :=
  directSumRight_faithful R P

example (P : IsoCategory (Matrix (Fin 2) (Fin 2) ℤ)) :
    ∃ (n : ℕ) (Q : IsoCategory (Matrix (Fin 2) (Fin 2) ℤ)),
      Nonempty (P ⊗ Q ≅ rankOnePower _ n) :=
  rankOne_cofinal _ P

example (P : IsoCategory (ZMod 1)) :
    ∃ (n : ℕ) (Q : IsoCategory (ZMod 1)), Nonempty (P ⊗ Q ≅ rankOnePower _ n) :=
  rankOne_cofinal _ P

end DirectSum

example (C : Type u) [CategoryTheory.Category.{v} C]
    [MonoidalCategory C] [SymmetricCategory C] : SymmetricCategory (Core C) :=
  inferInstance

section CompletionGrading

example (R : Type u) [Ring R] {X Y : GroupCompletionCategory R} (f : X ⟶ Y) :
    completionGrade R X = completionGrade R Y :=
  completionGrade_map R f

example (R : Type u) [Ring R] (P : IsoCategory Rᵐᵒᵖ) :
    completionGrade Rᵐᵒᵖ ((completionUnit Rᵐᵒᵖ).obj P) =
      (exactStructure Rᵐᵒᵖ).grothendieckClass P.of :=
  completionGrade_unit_obj Rᵐᵒᵖ P

example (R : Type u) [Ring R] (P : IsoCategory R) :
    completionGrade R (completionPair R P P) = 0 :=
  completionGrade_diagonal R P

example (n : ℕ) :
    completionGrade (Matrix (Fin 2) (Fin 2) ℤ)
      ((completionUnit _).obj (freeIso _ n)) = coreClass _ (freeIso _ n) :=
  completionGrade_unit_obj _ _

example (P : IsoCategory (ZMod 1)) :
    completionGrade (ZMod 1) ((completionUnit _).obj P) = coreClass _ P :=
  completionGrade_unit_obj _ P

end CompletionGrading
