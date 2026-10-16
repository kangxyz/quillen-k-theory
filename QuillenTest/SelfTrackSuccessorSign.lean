/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Prespectrum.SelfTrackSuccessorSign

/-! The finite successor equation retains the actual maps and the proved coordinate sign. -/
@[expose] public section
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
open CategoryTheory Quillen Quillen.LoopPrespectrum
universe u
namespace QuillenTest.SelfTrackSuccessorSign

/-- The one-higher original self-track class has the exact original successor sign. -/
theorem original_successor_sign {E F : LoopPrespectrum.{u}} {f : E ⟶ F}
    (H : Homotopy f f) (n m : ℕ)
    (a : HomotopyGroup.Pi (m + 2) (E.space n) (E.point n)) :
    H.homotopyClassOperation (n + 1) (m + 2) (structurePiMap E n (m + 1) a) =
      (structurePiMap F n (m + 2) (H.homotopyClassOperation n (m + 1) a))⁻¹ :=
  H.homotopyClassOperation_structure_sign n m a

/-- The successor map still evaluates the original structure map before uncurrying. -/
theorem original_structure_representative (E : LoopPrespectrum.{u}) (n m : ℕ)
    (p : GenLoop (Fin (m + 2)) (E.space n) (E.point n)) :
    structurePiMap E n (m + 1) ⟦p⟧ =
      (⟦loopUncurry (genLoopPostcomp (E.structureMap n) (E.map_point n) p)⟧ :
        HomotopyGroup.Pi (m + 3) (E.space (n + 1)) (E.point (n + 1))) :=
  structurePiMap_mk E n (m + 1) p

end QuillenTest.SelfTrackSuccessorSign
