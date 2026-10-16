/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.HomotopyGroups.GenLoopSelfTrackNaturality
public import Quillen.Topology.Prespectrum.SelfTrackHomotopyAdditivity

/-!
# Original-map naturality of the finite self-track operation

Precomposition retains the original input cube, and postcomposition retains
the original based map on every track and both normalization cancellations.
These are finite equations; no stable operation is defined here.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Quillen.LoopPrespectrum
variable {D E F G : LoopPrespectrum.{u}} {f : E ⟶ F}

/-- Postcomposition of the actual H-family induces the original one-higher homotopy map. -/
theorem Homotopy.homotopyClassOperation_postcomp (H : Homotopy f f) (j : F ⟶ G)
    (n m : ℕ) (a : HomotopyGroup.Pi (m + 1) (E.space n) (E.point n)) :
    (H.postcomp j).homotopyClassOperation n m a =
      piMap (m + 1) (j.map n) (j.map_point n) (H.homotopyClassOperation n m a) := by
  refine Quotient.inductionOn a (fun p ↦ ?_)
  exact (genLoopSelfTrackClass_naturality (j.map n) (j.map_point n) m _
    (H.genLoopPath n p)).symm

/-- Precomposition applies the original source map to the original sphere representative. -/
theorem Homotopy.homotopyClassOperation_precomp (H : Homotopy f f) (i : D ⟶ E)
    (n m : ℕ) (a : HomotopyGroup.Pi (m + 1) (D.space n) (D.point n)) :
    (H.precomp i).homotopyClassOperation n m a =
      H.homotopyClassOperation n m (piMap m (i.map n) (i.map_point n) a) := by
  refine Quotient.inductionOn a (fun _ ↦ ?_)
  rfl

/-- The finite homomorphism commutes with the supplied original target map. -/
theorem Homotopy.homotopyClassOperationHom_postcomp (H : Homotopy f f) (j : F ⟶ G)
    (n m : ℕ) :
    (H.postcomp j).homotopyClassOperationHom n m =
      (piMap (m + 2) (j.map n) (j.map_point n)).comp (H.homotopyClassOperationHom n m) := by
  ext a
  exact H.homotopyClassOperation_postcomp j n (m + 1) a

/-- The finite homomorphism commutes with the supplied original source map. -/
theorem Homotopy.homotopyClassOperationHom_precomp (H : Homotopy f f) (i : D ⟶ E)
    (n m : ℕ) :
    (H.precomp i).homotopyClassOperationHom n m =
      (H.homotopyClassOperationHom n m).comp (piMap (m + 1) (i.map n) (i.map_point n)) := by
  ext a
  exact H.homotopyClassOperation_precomp i n (m + 1) a

end Quillen.LoopPrespectrum
