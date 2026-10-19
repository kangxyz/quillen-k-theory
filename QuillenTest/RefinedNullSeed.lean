/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Topology.Prespectrum.RefinedNullSeed

/-! The independent cell and whole original null keep their actual time coordinates. -/
@[expose] public section
noncomputable section
open CategoryTheory Quillen.LoopPrespectrum
open scoped unitInterval
universe u
namespace QuillenTest.RefinedNullSeed
variable {E D C D' C' : Quillen.LoopPrespectrum.{u}} (f : E ⟶ D) (j : D ⟶ C)
  (r : D ⟶ D') (s : C ⟶ C') (j' : D' ⟶ C') (h : r ≫ j' = j ≫ s)
  (K : Homotopy (f ≫ r) (f ≫ r)) (N : Homotopy (f ≫ j) (zeroHom E C))

/-- The cell time belongs to the independently supplied cell, before the actual inclusion. -/
theorem cell_level (n : ℕ) (t : unitInterval) (x : E.space n) :
    (Quillen.LoopPrespectrum.RefinedNullSeed.cell f j r s j' h K).level n (t, x) =
      j'.map n (K.level n (t, x)) := rfl

/-- The whole original null height remains unchanged by the target refinement. -/
theorem null_level (n : ℕ) (t : unitInterval) (x : E.space n) :
    (Quillen.LoopPrespectrum.RefinedNullSeed.null f j s N).level n (t, x) =
      s.map n (N.level n (t, x)) := rfl

/-- The seed comparison uses these same original whole tracks and maps. -/
theorem seed_comparison (H : Homotopy f f) (hK : K = H.postcomp r) :
    Quillen.LoopPrespectrum.RefinedNullSeed.seed f j r s j' h K N =
      (H.postcomp j).nullLoopMap N ≫ parameterLoopingMap s :=
  Quillen.LoopPrespectrum.RefinedNullSeed.seed_eq f j r s j' h K N H hK

end QuillenTest.RefinedNullSeed
