/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Spectrum.GlobalUnitStableOperation
public import Quillen.Waldhausen.SConstruction.Iterated.SelfTrackKOperation

/-! # Inverse-unit operations on all original nonnegative K-groups -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes

/-- The actual inverse-unit operation inverts the output on every original K-class. -/
theorem perfectFlatUnitHomotopy_originalKOperation_inv {X Y : Scheme.{u}}
    (f : X ⟶ Y) [Flat f] (q : (Γ(X, ⊤))ˣ) (n : ℕ) (a : PerfectK Y n) :
    originalKSelfTrackOperation (perfectWaldhausen Y) (perfectWaldhausen X)
        (perfectFlatUnitHomotopy f q⁻¹) n a =
      (originalKSelfTrackOperation (perfectWaldhausen Y) (perfectWaldhausen X)
        (perfectFlatUnitHomotopy f q) n a)⁻¹ := by
  apply (originalKStableEquiv (perfectWaldhausen X) (n + 1)).injective
  change originalKStableEquiv (perfectWaldhausen X) (n + 1)
      (Additive.ofMul (originalKSelfTrackOperation (perfectWaldhausen Y) (perfectWaldhausen X)
        (perfectFlatUnitHomotopy f q⁻¹) n a)) =
    originalKStableEquiv (perfectWaldhausen X) (n + 1)
      (-Additive.ofMul (originalKSelfTrackOperation (perfectWaldhausen Y) (perfectWaldhausen X)
        (perfectFlatUnitHomotopy f q) n a))
  rw [map_neg, originalKSelfTrackOperation_stable, originalKSelfTrackOperation_stable,
    perfectFlatUnitHomotopy_stableOperation_inv]
  rfl

end Quillen.PerfectComplexes
