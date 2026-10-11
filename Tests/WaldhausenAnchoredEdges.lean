/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Waldhausen.GrothendieckComparison.EdgeNormalization
public import Quillen.Waldhausen.GrothendieckComparison.ClassicalMap

/-! Consumers of actual edge normalization use arbitrary original diagonal
one-simplices and their coherent original zero-object anchors. -/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits Quillen.Waldhausen
open scoped Simplicial Topology
universe u
namespace Quillen.Tests.WaldhausenAnchoredEdges
variable {C : Type u} [SmallCategory C] (W : Structure C)

/-- Every original diagonal edge closed with the actual original zero tracks
is the canonical image of its original source-row object generator. -/
theorem arbitrary_grid_original_generator (X : (sSet W.cof W.weq) _⦋1⦌) :
    W.zeroAnchorHom (W.gridZero X 0 0) ≫ W.gridPathHom X ≫
      inv (W.zeroAnchorHom (W.gridZero X 1 1)) =
        W.kZeroFundamentalGroupEquiv
          (AlgebraicGrothendieck.grothendieckToKZero W
            (Multiplicative.ofAdd (AlgebraicGrothendieck.objectClass W
              (X.val.obj (grid 0 0 1 (by decide)))))) := by
  rw [AlgebraicGrothendieck.grothendieckToKZero_objectClass,
    W.kZeroFundamentalGroupEquiv_objectClass]
  exact W.gridPathHom_normalization_closed X

/-- The arbitrary original edge yields an actual fine class in the canonical
classical image; no arbitrary continuous loop is substituted for that edge. -/
theorem arbitrary_grid_classical_image (X : (sSet W.cof W.weq) _⦋1⦌) :
    W.kZeroFundamentalGroupEquiv.symm
      (W.zeroAnchorHom (W.gridZero X 0 0) ≫ W.gridPathHom X ≫
        inv (W.zeroAnchorHom (W.gridZero X 1 1))) ∈
      Set.range (AlgebraicGrothendieck.grothendieckToKZero W) := by
  rw [arbitrary_grid_original_generator W X, MulEquiv.symm_apply_apply]
  exact ⟨_, rfl⟩

/-- An original zero-object round trip contributes no hidden loop to the anchors. -/
theorem original_zero_round_trip (Z : Structure.ZeroObjects (C := C)) :
    W.zeroAnchorHom Z ≫ W.zeroTrackHom Z W.chosenZeroObject =
      𝟙 (FundamentalGroupoid.mk W.kBasepoint) := by
  change W.zeroTrackHom W.chosenZeroObject Z ≫
    W.zeroTrackHom Z W.chosenZeroObject = _
  rw [W.zeroTrackHom_comp, W.zeroTrackHom_self]
  rfl

end Quillen.Tests.WaldhausenAnchoredEdges
