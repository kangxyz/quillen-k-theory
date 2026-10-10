/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Limits.Final

/-! Actual finite-tail colimit isomorphisms with both original stage-inclusion formulas. -/
@[expose] public section


noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v
namespace Quillen

/-- The actual shift of the original natural-number indexing category. -/
def sequentialShiftFunctor (t : ℕ) : ℕ ⥤ ℕ :=
  (show Monotone (fun n : ℕ ↦ t+n) from fun _ _ h ↦ Nat.add_le_add_left h t).functor

instance instFinalSequentialShiftFunctor (t : ℕ) : (sequentialShiftFunctor t).Final :=
  (Monotone.final_functor_iff _).mpr (fun n ↦ ⟨n,Nat.le_add_left n t⟩)

/-- Dropping finitely many original stages preserves the actual sequential colimit. -/
def sequentialTailColimitIso {C : Type u} [Category.{v} C]
    (F : ℕ ⥤ C) [HasColimit F] (t : ℕ) :
    colimit (sequentialShiftFunctor t ⋙ F) ≅ colimit F :=
  Functor.Final.colimitIso (sequentialShiftFunctor t) F

@[reassoc (attr := simp)] theorem sequentialTailColimitIso_ι_hom
    {C : Type u} [Category.{v} C] (F : ℕ ⥤ C) [HasColimit F] (t n : ℕ) :
    colimit.ι (sequentialShiftFunctor t ⋙ F) n ≫ (sequentialTailColimitIso F t).hom =
      colimit.ι F (t+n) :=
  Functor.Final.ι_colimitIso_hom (sequentialShiftFunctor t) F n

@[reassoc (attr := simp)] theorem sequentialTailColimitIso_ι_inv
    {C : Type u} [Category.{v} C] (F : ℕ ⥤ C) [HasColimit F] (t n : ℕ) :
    colimit.ι F (t+n) ≫ (sequentialTailColimitIso F t).inv =
      colimit.ι (sequentialShiftFunctor t ⋙ F) n :=
  Functor.Final.ι_colimitIso_inv (sequentialShiftFunctor t) F n

end Quillen
