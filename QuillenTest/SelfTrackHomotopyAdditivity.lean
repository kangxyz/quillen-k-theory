/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Prespectrum.SelfTrackHomotopyAdditivity

/-! Actual finite self-track additivity in input degree at least two. -/
@[expose] public section
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
open CategoryTheory Quillen Quillen.LoopPrespectrum
universe u
namespace QuillenTest.SelfTrackHomotopyAdditivity

/-- The original quotient function respects spatial multiplication in input degree at least two. -/
theorem original_finite_track_product {E F : LoopPrespectrum.{u}} {f : E ⟶ F}
    (H : Homotopy f f) (n m : ℕ)
    (a b : HomotopyGroup.Pi (m + 2) (E.space n) (E.point n)) :
    H.homotopyClassOperation n (m + 1) (a * b) =
      H.homotopyClassOperation n (m + 1) a * H.homotopyClassOperation n (m + 1) b :=
  H.homotopyClassOperation_mul n m a b

/-- The homomorphism still evaluates exactly the original cube and H-family. -/
theorem original_finite_track_hom_representative {E F : LoopPrespectrum.{u}} {f : E ⟶ F}
    (H : Homotopy f f) (n m : ℕ)
    (p : GenLoop (Fin (m + 2)) (E.space n) (E.point n)) :
    H.homotopyClassOperationHom n m ⟦p⟧ =
      genLoopSelfTrackClass (m + 1) _ (H.genLoopPath n p) := rfl

end QuillenTest.SelfTrackHomotopyAdditivity
