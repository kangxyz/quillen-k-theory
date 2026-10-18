/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.KTheory.Plus.StableZeroFiberHomology
public import Quillen.Topology.HomotopyFiber.H2Perfectness
public import Quillen.KTheory.Field.SteinbergFiberComparison

/-!
# Perfectness of the original stable completion fiber group

For every ring, the constructed simply connected cover and its actual pullback
supply the geometric and integral homology hypotheses of the proved low-degree
criterion. The original endpoint-aware fiber map transfers perfectness to the
literal stable-zero homotopy fiber at its canonical constant-path point.
The field theorem uses the existing `StableFiberPiOne` alias.
-/

@[expose] public section
noncomputable section
universe u
namespace Quillen.FiniteProjectiveModule.StableCompletion

/-- The original stable-zero homotopy fiber has perfect Pi one for every ring. -/
theorem stableZeroFiber_piOne_isPerfect (R : Type u) [Ring R] :
    Group.IsPerfect (HomotopyGroup.Pi 1
      (HomotopyFiber (stableZeroMap R) (stableZeroMap R (stableBase R)))
      (HomotopyFiber.basepoint (stableZeroMap R) (stableZeroMap R (stableBase R))
        (stableBase R) rfl)) := by
  obtain ⟨T, t, setup⟩ := exists_stableZeroCover_homologicalSetup R
  let := t
  obtain ⟨q, e, he, _hq, _hqs, hT, hP, hp, hH, hm⟩ := setup
  let := hT
  let := hP
  let := hp
  let : Group.IsPerfect
      (HomotopyGroup.Pi 1 (HomotopyFiber (Covering.Pullback.lift (stableZeroMap R) q) e)
        (HomotopyFiber.basepoint (Covering.Pullback.lift (stableZeroMap R) q) e
          (stableZeroCoverPoint R q e he) rfl)) :=
    HomotopyFiber.piOne_isPerfect_of_singular_quasiIso
      (Covering.Pullback.lift (stableZeroMap R) q) e (stableZeroCoverPoint R q e he) rfl hH
  exact Group.IsPerfect.ofSurjective hm.surjective

/-- The actual field fiber group already used by the Steinberg comparison is perfect. -/
theorem stableFiberPiOne_isPerfect (F : Type u) [Field F] :
    Group.IsPerfect (StableFiberPiOne F) :=
  stableZeroFiber_piOne_isPerfect F

end Quillen.FiniteProjectiveModule.StableCompletion
