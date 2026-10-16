/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Prespectrum.SelfTrackStableOperation
public import Quillen.Waldhausen.SConstruction.Iterated.StableHomotopy

/-!
# Original nonnegative K-group operations of actual self-tracks

The proved stable operation is transported through the existing comparisons
with the unchanged original K-groups, including K-zero. This produces genuine
group homomorphisms, not only functions on object representatives. It does not
identify a scalar loop's object value or prove a localization boundary formula.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Quillen.LoopPrespectrum
universe u v
namespace Quillen.Waldhausen.IteratedS
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
variable (W : Structure C) (V : Structure D)
variable {f : originalPrespectrum W ⟶ originalPrespectrum V}

/-- The original comparison transports the actual degree-raising stable operation. -/
def originalKSelfTrackOperationAdd (H : Homotopy f f) (n : ℕ) :
    Additive (W.K n) →+ Additive (V.K (n + 1)) :=
  (originalKStableEquiv V (n + 1)).symm.toAddMonoidHom.comp
    ((H.stableOperation (n : ℤ)).hom.comp (originalKStableEquiv W n).toAddMonoidHom)

/-- Every original nonnegative K-group receives the genuine self-track homomorphism. -/
def originalKSelfTrackOperation (H : Homotopy f f) (n : ℕ) : W.K n →* V.K (n + 1) :=
  (originalKSelfTrackOperationAdd W V H n).toMultiplicative

/-- The operation retains the exact original stable comparison on every original K-class. -/
theorem originalKSelfTrackOperation_stable (H : Homotopy f f) (n : ℕ) (a : W.K n) :
    originalKStableEquiv V (n + 1)
        (Additive.ofMul (originalKSelfTrackOperation W V H n a)) =
      H.stableOperation (n : ℤ) (originalKStableEquiv W n (Additive.ofMul a)) := by
  exact (originalKStableEquiv V (n + 1)).apply_symm_apply _

/-- The unchanged stable comparison uniquely determines the operation on the original K-group. -/
theorem originalKSelfTrackOperation_unique (H : Homotopy f f) (n : ℕ)
    (g : W.K n →* V.K (n + 1))
    (hg : ∀ a, originalKStableEquiv V (n + 1) (Additive.ofMul (g a)) =
      H.stableOperation (n : ℤ) (originalKStableEquiv W n (Additive.ofMul a))) :
    g = originalKSelfTrackOperation W V H n := by
  ext a
  have h := (hg a).trans (originalKSelfTrackOperation_stable W V H n a).symm
  exact (originalKStableEquiv V (n + 1)).injective h

end Quillen.Waldhausen.IteratedS
