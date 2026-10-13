/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Spectrum.BoundedFlatPullback
public import Quillen.Topology.Prespectrum.HomotopyTransport

/-! # The original geometric square track with explicit endpoint transport

The existing square construction retains the whole reversed first composition track followed
by the second composition track. Only its endpoint equality witness is transported.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
universe u
namespace Quillen.PerfectComplexes

private theorem transported_trans_level {E F : LoopPrespectrum.{u}}
    {a b c d : E ⟶ F} (H : Homotopy c d) (K : Homotopy a b) (e : b = c) (n : ℕ) :
    (K.trans (by rw [← e] at H; exact H)).level n = (K.trans (H.cast e.symm rfl)).level n := by
  cases e
  rfl

/-- The original geometric square retains both complete composition tracks, with an explicit
transport at their common endpoint. -/
theorem boundedFlatPerfectPrespectrumSquareHomotopy_level {X Y Z T : Scheme.{u}}
    (p : X ⟶ Y) (v : Y ⟶ Z) (q : X ⟶ T) (w : T ⟶ Z)
    (h : p ≫ v = q ≫ w) (n : ℕ) :
    (boundedFlatPerfectPrespectrumSquareHomotopy p v q w h).level n =
      ((boundedFlatPerfectPrespectrumCompHomotopy p v).symm.trans
        ((boundedFlatPerfectPrespectrumCompHomotopy q w).cast
          (congrArg boundedFlatPerfectPrespectrumMap h).symm rfl)).level n := by
  exact transported_trans_level (boundedFlatPerfectPrespectrumCompHomotopy q w)
    (boundedFlatPerfectPrespectrumCompHomotopy p v).symm
    (congrArg boundedFlatPerfectPrespectrumMap h) n

end Quillen.PerfectComplexes
