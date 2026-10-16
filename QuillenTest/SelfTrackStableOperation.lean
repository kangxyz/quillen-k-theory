/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Prespectrum.SelfTrackStableOperation

/-! Actual representatives and actual integer-graded colimit legs of the self-track operation. -/
@[expose] public section
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
open CategoryTheory CategoryTheory.Limits Quillen Quillen.LoopPrespectrum
universe u
namespace QuillenTest.SelfTrackStableOperation

/-- The finite stage still evaluates the same original based cube and same original H-family. -/
theorem original_stage_representative {E F : LoopPrespectrum.{u}} {f : E ⟶ F}
    (H : Homotopy f f) (d : ℤ) (n : ℕ)
    (p : GenLoop (Fin (d.toNat + n + 2))
      (E.space ((-d).toNat + n + 2)) (E.point ((-d).toNat + n + 2))) :
    H.stableStageOperation d n (Additive.ofMul
      (⟦p⟧ : HomotopyGroup.Pi (d.toNat + n + 2)
        (E.space ((-d).toNat + n + 2)) (E.point ((-d).toNat + n + 2)))) =
      Additive.ofMul (genLoopSelfTrackClass (d.toNat + n + 1) _
        (H.genLoopPath ((-d).toNat + n + 2) p)) := rfl

/-- The final original stage leg includes its displayed sign and exact integer-degree tail. -/
theorem original_stable_stage_leg {E F : LoopPrespectrum.{u}} {f : E ⟶ F}
    (H : Homotopy f f) (d : ℤ) (n : ℕ) :
    stableHomotopyι E d n ≫ H.stableOperation d =
      ((-1 : ℤ) ^ n • H.stableStageOperation d n) ≫
        (shiftedStableReindexIso F d n).hom ≫
          stableHomotopyι F (d + 1) (parameterStableOffset d + n) :=
  H.stableOperation_ι d n

end QuillenTest.SelfTrackStableOperation
