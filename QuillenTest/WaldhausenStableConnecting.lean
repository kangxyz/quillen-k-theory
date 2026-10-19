/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Waldhausen.Fibration.StableConnectingComparison

/-!
Regression properties of the signed original Waldhausen stable boundary:
the K1-to-K0 fiber classes cancel, and the intrinsic lift boundary kills
the unchanged original change-of-weak-equivalences K-map in every positive degree.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Quillen Quillen.Waldhausen Quillen.Waldhausen.Fibration
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
universe u v

namespace QuillenTest.WaldhausenStableConnecting

variable {C : Type u} [Category.{v} C] {V : Structure C}
  (N : NestedWeakEquivalences V)

/-- The actual intrinsic K1 boundary cancels its unchanged original K0 boundary class. -/
theorem Kone_boundary_add_original_Kzero
    (h : IsWeakHomotopyEquivalence (canonicalFiberMap N)) (a : N.coarse.K 1) :
    let := acyclicPrespectrumFiberLift_nonneg_isIso N h 0
    stableFiberLiftConnecting (acyclicInclusionPrespectrumMap N) (changeWeakPrespectrumMap N)
        (acyclicPrespectrumNullhomotopy N) (0 : ℤ)
        (eqToHom (congrArg (stableHomotopyGroup (originalPrespectrum N.coarse))
          (show ((0 + 1 : ℕ) : ℤ) = (0 : ℤ) + 1 from rfl))
          (originalKStableEquiv N.coarse 1 (Additive.ofMul a))) +
      originalKStableEquiv (acyclicStructure N) 0
        (Additive.ofMul (changeWeakConnectingHom N h 0 a)) = 0 := by
  let := acyclicPrespectrumFiberLift_nonneg_isIso N h 0
  dsimp only
  exact add_eq_zero_iff_eq_neg.mpr (originalKStableEquiv_liftConnecting_sign N h 0 rfl a)

/-- Exactness of the original K-maps forces the specified lift boundary to vanish. -/
theorem lift_boundary_changeWeak_eq_zero
    (h : IsWeakHomotopyEquivalence (canonicalFiberMap N)) (n : ℕ)
    (κ : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1) (a : V.K (n + 1)) :
    let := acyclicPrespectrumFiberLift_nonneg_isIso N h n
    stableFiberLiftConnecting (acyclicInclusionPrespectrumMap N) (changeWeakPrespectrumMap N)
        (acyclicPrespectrumNullhomotopy N) (n : ℤ)
        (eqToHom (congrArg (stableHomotopyGroup (originalPrespectrum N.coarse)) κ)
          (originalKStableEquiv N.coarse (n + 1)
            (Additive.ofMul (KMap (changeWeak_exact N) (n + 1) a)))) = 0 := by
  let := acyclicPrespectrumFiberLift_nonneg_isIso N h n
  dsimp only
  have hm : KMap (changeWeak_exact N) (n + 1) a ∈
      (KMap (changeWeak_exact N) (n + 1)).range := ⟨a, rfl⟩
  rw [range_changeWeak_eq_ker_changeWeakConnectingHom N h n] at hm
  have hz : changeWeakConnectingHom N h n (KMap (changeWeak_exact N) (n + 1) a) = 1 := hm
  rw [originalKStableEquiv_liftConnecting_sign N h n κ, hz,
    ofMul_one, map_zero, neg_zero]

end QuillenTest.WaldhausenStableConnecting
