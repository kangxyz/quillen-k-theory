/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.SelfTrackKOperation

/-! # Unchanged original K-zero and higher-group self-track consumers -/
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
@[expose] public section
noncomputable section
open CategoryTheory Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
universe u v
namespace QuillenTest.SelfTrackKOperation
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
variable (W : Quillen.Waldhausen.Structure C) (V : Quillen.Waldhausen.Structure D)
variable {f : originalPrespectrum W ⟶ originalPrespectrum V}

/-- K-zero is included with the exact original stabilization, not an object-only map. -/
theorem original_kzero_stabilization (H : Homotopy f f) (a : W.K 0) :
    originalKStableEquiv V 1 (Additive.ofMul (originalKSelfTrackOperation W V H 0 a)) =
      H.stableOperation 0 (originalKStableEquiv W 0 (Additive.ofMul a)) :=
  originalKSelfTrackOperation_stable W V H 0 a

/-- The original group law is preserved in every nonnegative input degree. -/
theorem original_group_product (H : Homotopy f f) (n : ℕ) (a b : W.K n) :
    originalKSelfTrackOperation W V H n (a * b) =
      originalKSelfTrackOperation W V H n a * originalKSelfTrackOperation W V H n b :=
  (originalKSelfTrackOperation W V H n).map_mul a b

end QuillenTest.SelfTrackKOperation
