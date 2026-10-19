/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Waldhausen.Fibration.StableConnectingComparison

/-!
A client detects vanishing of the specified stable fiber-lift boundary using
the unchanged original multiplicative K-boundary, including its degree-zero target.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Quillen Quillen.Waldhausen Quillen.Waldhausen.Fibration
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
universe u v

namespace Consumer.WaldhausenStableConnecting

/-- Original K-classes detect zero under the intrinsic signed stable boundary in every degree. -/
theorem lift_boundary_eq_zero_iff_original_boundary_eq_one
    {C : Type u} [Category.{v} C] {V : Structure C} (N : NestedWeakEquivalences V)
    (h : IsWeakHomotopyEquivalence (canonicalFiberMap N)) (n : ℕ)
    (κ : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1) (a : N.coarse.K (n + 1)) :
    let := acyclicPrespectrumFiberLift_nonneg_isIso N h n
    stableFiberLiftConnecting (acyclicInclusionPrespectrumMap N) (changeWeakPrespectrumMap N)
        (acyclicPrespectrumNullhomotopy N) (n : ℤ)
        (eqToHom (congrArg (stableHomotopyGroup (originalPrespectrum N.coarse)) κ)
          (originalKStableEquiv N.coarse (n + 1) (Additive.ofMul a))) = 0 ↔
      changeWeakConnectingHom N h n a = 1 := by
  let := acyclicPrespectrumFiberLift_nonneg_isIso N h n
  dsimp only
  rw [originalKStableEquiv_liftConnecting_sign N h n κ, neg_eq_zero]
  constructor
  · intro ha
    have hb : Additive.ofMul (changeWeakConnectingHom N h n a) = 0 :=
      (originalKStableEquiv (acyclicStructure N) n).injective
        (ha.trans (map_zero _).symm)
    exact ofMul_eq_zero.mp hb
  · intro ha
    rw [ha, ofMul_one, map_zero]

end Consumer.WaldhausenStableConnecting
