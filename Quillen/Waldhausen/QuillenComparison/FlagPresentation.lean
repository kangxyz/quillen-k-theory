/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Waldhausen.QuillenComparison.FlagMaps
public import Quillen.Waldhausen.QuillenComparison.InitialFlag

/-! # Exact rows and canonical completions of their initial flags -/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
universe v u

namespace Quillen.Waldhausen.QuillenComparison

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
variable (E : Quillen.ExactStructure C) {n : SimplexCategory}

/-- The initial flag of an exact row is genuinely admissible. -/
theorem initialFlag_inflation (F : Row E n) {i j : Fin (n.len + 1)} (f : i ⟶ j) :
    E.inflation ((initialFlag E F).map f) :=
  F.simplex.cofibration 0 0 i j (Fin.zero_le _) (leOfHom f)

/-- Its first object is genuinely zero. -/
theorem initialFlag_zero (F : Row E n) : IsZero ((initialFlag E F).obj 0) :=
  F.simplex.zero 0 0

/-- Uniqueness of actual cokernels compares a completed flag with its original exact row. -/
def completedInitialIsoAt (F : Row E n) (p : Interval n) :
    (quotientDiagram E (initialFlag E F) (initialFlag_inflation E F)).obj p ≅ F.diagram.obj p :=
  (flagQuotientIsCokernel E (initialFlag_inflation E F) p).coconePointUniqueUpToIso
    (initialCokernel E F p)

@[reassoc (attr := simp)]
theorem flagQuotient_completedInitialIsoAt (F : Row E n) (p : Interval n) :
    flagQuotient E (initialFlag E F) (initialFlag_inflation E F) p ≫
      (completedInitialIsoAt E F p).hom = initialQuotient E F p :=
  (flagQuotientIsCokernel E (initialFlag_inflation E F) p).comp_coconePointUniqueUpToIso_hom
    (initialCokernel E F p) WalkingParallelPair.one

/-- Every existing exact row is canonically isomorphic to the actual cokernel
completion of its own initial flag. -/
def completedInitialIso (F : Row E n) :
    (flagRow E (initialFlag E F) (initialFlag_inflation E F)) ⟶ F :=
  NatIso.ofComponents (completedInitialIsoAt E F) (by
    intro p q f
    let : Epi (flagQuotient E (initialFlag E F) (initialFlag_inflation E F) p) :=
      inferInstance
    apply (cancel_epi (flagQuotient E (initialFlag E F) (initialFlag_inflation E F) p)).1
    dsimp only [flagRow]
    rw [flagQuotient_naturality_assoc, flagQuotient_completedInitialIsoAt,
      ← Category.assoc, flagQuotient_completedInitialIsoAt]
    simp only [initialFlag, initialQuotient, CategoryTheory.Functor.comp_map, ← F.diagram.map_comp]
    congr 1)

variable (A : Fin (n.len + 1) ⥤ C)
variable (hA : ∀ {i j} (f : i ⟶ j), E.inflation (A.map f))

/-- For a zero-start flag, quotienting by the initial object changes no initial
flag object up to its canonical quotient isomorphism. -/
def initialCompletionIso (hzero : IsZero (A.obj 0)) :
    A ≅ initialFlag E (flagRow E A hA) := by
  have hiso (i : Fin (n.len + 1)) : IsIso (flagQuotient E A hA (interval 0 i (Fin.zero_le _))) :=
    CokernelCofork.IsColimit.isIso_π
      (CokernelCofork.ofπ (flagQuotient E A hA (interval 0 i (Fin.zero_le _)))
        (flagQuotient_zero E hA _)) (flagQuotientIsCokernel E hA _) (hzero.eq_of_src _ _)
  letI (i : Fin (n.len + 1)) : IsIso (flagQuotient E A hA (interval 0 i (Fin.zero_le _))) := hiso i
  exact NatIso.ofComponents
    (fun i ↦ asIso (flagQuotient E A hA (interval 0 i (Fin.zero_le _)))) (by
      intro i j f
      exact (flagQuotient_naturality E A hA ((initialIntervals n).map f)).symm)

end Quillen.Waldhausen.QuillenComparison
