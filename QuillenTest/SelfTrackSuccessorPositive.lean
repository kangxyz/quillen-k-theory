/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Prespectrum.SelfTrackSuccessorPositive

/-! # The original degree-one successor representative and sign -/
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
@[expose] public section
noncomputable section
open CategoryTheory Quillen Quillen.LoopPrespectrum
universe u
namespace QuillenTest.SelfTrackSuccessorPositive

/-- The first positive input retains independent original track and structure coordinates. -/
theorem original_degree_one_representative {E F : LoopPrespectrum.{u}} {f : E ⟶ F}
    (H : Homotopy f f) (n : ℕ) (p : GenLoop (Fin 1) (E.space n) (E.point n)) :
    H.genLoopNormalizedSelfTrackCubeSecond (n + 1) 0
        (loopUncurry (genLoopPostcomp (E.structureMap n) (E.map_point n) p)) =
      transposeGenLoop (0 : Fin 3) 1 Fin.zero_ne_one
        (loopUncurry (genLoopPostcomp (F.structureMap n) (F.map_point n)
          (genLoopNormalizedSelfTrackCube 0 _ (H.genLoopPath n p)))) :=
  H.genLoopNormalizedSelfTrackCubeSecond_structure_positive n 0 p

/-- The successor sign includes input pi-one without assuming its operation is a homomorphism. -/
theorem original_degree_one_sign {E F : LoopPrespectrum.{u}} {f : E ⟶ F}
    (H : Homotopy f f) (n : ℕ) (a : HomotopyGroup.Pi 1 (E.space n) (E.point n)) :
    H.homotopyClassOperation (n + 1) 1 (structurePiMap E n 0 a) =
      (structurePiMap F n 1 (H.homotopyClassOperation n 0 a))⁻¹ :=
  H.homotopyClassOperation_structure_sign_positive n 0 a

end QuillenTest.SelfTrackSuccessorPositive
