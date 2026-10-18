/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Algebra.Group.StableSteinbergSchur
public import Quillen.KTheory.Plus.StableZeroFiberHomology

/-!
# The Schur comparison for the actual stable zero-cover pullback

The original chains, signs, maps, basepoints and stated hypotheses are retained.
-/
@[expose] public section

section

open groupHomology.IntegralBar
open Quillen.StableSteinberg.Schur
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory
namespace Quillen.FiniteProjectiveModule.StableCompletion
open groupHomology.IntegralBar Quillen.StableSteinberg.Schur
variable (F : Type u) [Field F] {T : Type (u + 1)} [TopologicalSpace T]
  (q : C(T, ZeroComponent F)) (e : T) (he : q e = stableZeroMap F (stableBase F))
  (hq : IsCoveringMap q) [SimplyConnectedSpace T]

/-- The actual cover pullback Pi one is identified with elementary F through its ORIGINAL
first projection and the original stable-group classifying-space equivalence. -/
def coverElementaryEquiv :
    HomotopyGroup.Pi 1 (Covering.Pullback.Space (stableZeroMap F) q)
      (stableZeroCoverPoint F q e he) ≃* StableGeneralLinear.elementary F := by
  let c := Covering.Pullback.piOneKernelEquiv (stableZeroMap F) q hq
    (stableZeroCoverPoint F q e he)
  have hk : (piMap 0 (stableZeroMap F) (stableZeroCoverPoint F q e he).property).ker =
      stableElementaryPiOneSubgroup F := by
    have hraw (y : ZeroComponent F) (h : stableZeroMap F (stableBase F) = y) :
        (piMap 0 (stableZeroMap F) h).ker = stableElementaryPiOneSubgroup F := by
      subst y
      exact stableZeroMap_rawPiOne_kernel F
    exact hraw (q e) he.symm
  exact (c.trans (MulEquiv.subgroupCongr hk)).trans
    ((GroupoidClassifying.singleObjPiOneEquiv (StableGeneralLinear.Group F)).subgroupMap
      (StableGeneralLinear.elementary F)).symm

/-- The displayed identification retains precisely the original based first-projection map. -/
theorem coverElementaryEquiv_apply
    (a : HomotopyGroup.Pi 1 (Covering.Pullback.Space (stableZeroMap F) q)
      (stableZeroCoverPoint F q e he)) :
    (coverElementaryEquiv F q e he hq a : StableGeneralLinear.Group F) =
      (GroupoidClassifying.singleObjPiOneEquiv (StableGeneralLinear.Group F)).symm
        (piMap 0 (Covering.Pullback.projection (stableZeroMap F) q)
          (x := stableZeroCoverPoint F q e he) rfl a) := rfl

/-- The original Steinberg kernel identifies with actual integral bar H-two of the SAME
cover-pullback Pi-one group. No singular-to-bar comparison or boundary calibration is assumed. -/
def stablePullbackIntegerSchurEquiv : (StableSteinberg.toElementary F).ker ≃*
    Multiplicative (integerBarH2 (HomotopyGroup.Pi 1
      (Covering.Pullback.Space (stableZeroMap F) q) (stableZeroCoverPoint F q e he))) := by
  let := stableZeroCoverPullback_piOne_isPerfect F q e he hq
  exact integerSchurAlongEquiv.{u, u + 1} F (coverElementaryEquiv F q e he hq)

end Quillen.FiniteProjectiveModule.StableCompletion

end
