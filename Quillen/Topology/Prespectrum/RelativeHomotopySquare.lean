/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Topology.Prespectrum.HomotopySquare
public import Quillen.Topology.Prespectrum.RelativeHomotopy

/-!
# Fixed-boundary squares from relative homotopies

The actual two-parameter map of a relative homotopy is a square with constant
endpoint tracks. This conversion retains every value and the independent
prespectrum structure coordinate.
-/
@[expose] public section

noncomputable section
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Quillen.LoopPrespectrum.Homotopy.RelHomotopy
variable {E F : LoopPrespectrum.{u}} {f g : E ⟶ F} {H K : Homotopy f g}

/-- A relative comparison gives its literal square with fixed endpoint tracks. -/
def toFixedSquare (J : H.RelHomotopy K) :
    H.Square K (Homotopy.refl f) (Homotopy.refl g) where
  level n := (J.level n).toHomotopy.toContinuousMap
  at_zero n s x := (J.level n).apply_zero (s, x)
  at_one n s x := (J.level n).apply_one (s, x)
  left n r x := ((J.level n).eq_fst r (x := (0, x)) (Or.inl rfl)).trans (H.at_zero n x)
  right n r x := ((J.level n).eq_fst r (x := (1, x)) (Or.inr (Or.inl rfl))).trans (H.at_one n x)
  at_point n r s := ((J.level n).eq_fst r (x := (s, E.point n))
    (Or.inr (Or.inr rfl))).trans (H.at_point n s)
  comm := J.comm

/-- The conversion preserves the full continuous comparison map. -/
@[simp] theorem toFixedSquare_level (J : H.RelHomotopy K) (n : ℕ) :
    J.toFixedSquare.level n = (J.level n).toHomotopy.toContinuousMap := rfl

end Quillen.LoopPrespectrum.Homotopy.RelHomotopy
