/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.SelfTrackKOperationLevelOne
public import Quillen.Topology.Prespectrum.SelfTrackPath

/-!
# Original K-zero evaluation on a supplied actual path

An explicit original small-model representative equality identifies the
K-zero input with a supplied based path. The level-one successor inverse
and the literal track/spatial normalization inverse then cancel. The result
is the forward original K-one normalization of the actual path self-track.
No representative is selected, and no geometric scalar value is assumed.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Quillen.LoopPrespectrum
universe u v
namespace Quillen.Waldhausen.IteratedS
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (W : Structure C) (V : Structure D)
  {f : originalPrespectrum W ⟶ originalPrespectrum V}

/-- On the supplied original K-zero representative, the two proved inverse signs cancel. -/
theorem originalKSelfTrackOperation_path (H : Homotopy f f) (a : W.K 0)
    (γ : Path ((originalPrespectrum W).point 1) ((originalPrespectrum W).point 1))
    (hγ : W.smallModelKEquiv 0 a = ⟦(genLoopHomeomorphOfUnique (Fin 1)).symm γ⟧) :
    V.smallModelKEquiv 1 (originalKSelfTrackOperation W V H 0 a) =
      loopKOneNormalization (basedLoopMap (f.map 1) (f.map_point 1) γ)
        ⟦H.pathSelfTrack 1 γ⟧ := by
  rw [originalKSelfTrackOperation_levelOne, hγ]
  exact (congrArg
    (fun b : HomotopyGroup.Pi 2 ((originalPrespectrum V).space 1)
      ((originalPrespectrum V).point 1) ↦ b⁻¹)
    (H.homotopyClassOperation_finOne 1 γ)).trans (inv_inv _)

end Quillen.Waldhausen.IteratedS
