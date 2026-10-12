/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module
public import Quillen.KTheory.Plus.StableProjectiveTelescope
public import Mathlib.Data.ZMod.Basic

/-!
# Original matrix-to-projective telescope consumers

The original functor lifts arrows uniquely, preserves the specified identity
chain, and retains these properties over the zero ring.
-/

@[expose] public section
noncomputable section
open CategoryTheory
universe u
namespace Quillen.FiniteProjectiveModule.StableFreeRight
variable (R : Type u) [Ring R]

/-- An arbitrary arrow between original free vertices has a unique original matrix lift. -/
theorem original_arrow_unique
    (X Y : StableGeneralLinear.GrothendieckModel.Telescope R)
    (f : (telescopeFunctor R).obj X ⟶ (telescopeFunctor R).obj Y) :
    ∃! g : X ⟶ Y, (telescopeFunctor R).map g = f := by
  obtain ⟨g, hg⟩ := (telescopeFunctor R).map_surjective f
  refine ⟨g, hg, ?_⟩
  intro h hh
  exact (telescopeFunctor R).map_injective (hh.trans hg.symm)

/-- The original identity matrix chain remains exactly the specified right-telescope chain. -/
theorem original_identity_chain (n m : ℕ) (h : n ≤ m) :
    (telescopeFunctor R).map ((matrixSequence R).map (homOfLE h)) =
      (stageSequence R).map (homOfLE h) := by
  change (stageSequence R).map (homOfLE h) ≫ stageAction R m 1 = _
  rw [map_one]
  exact Category.comp_id _

/-- The same original-arrow lifting theorem includes the zero ring. -/
theorem zero_ring_original_arrow_unique
    (X Y : StableGeneralLinear.GrothendieckModel.Telescope (ZMod 1))
    (f : (telescopeFunctor (ZMod 1)).obj X ⟶ (telescopeFunctor (ZMod 1)).obj Y) :
    ∃! g : X ⟶ Y, (telescopeFunctor (ZMod 1)).map g = f :=
  original_arrow_unique _ X Y f

end Quillen.FiniteProjectiveModule.StableFreeRight
