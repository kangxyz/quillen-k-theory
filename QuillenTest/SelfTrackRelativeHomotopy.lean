/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Prespectrum.SelfTrackRelativeHomotopy
public import QuillenTest.SelfTrackStableConcatenation

/-! # Supplied relative tracks compare original finite and negative stable operations -/
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
@[expose] public section
noncomputable section
open CategoryTheory Quillen Quillen.LoopPrespectrum
open scoped Topology
universe u
namespace QuillenTest.SelfTrackRelativeHomotopy
variable {E F : LoopPrespectrum.{u}} {f : E ⟶ F} {H K : Homotopy f f}

/-- A supplied whole relative comparison already identifies the original Pi-one operation. -/
theorem pi_one_comparison (J : H.RelHomotopy K) (n : ℕ)
    (a : HomotopyGroup.Pi 1 (E.space n) (E.point n)) :
    H.homotopyClassOperation n 0 a = K.homotopyClassOperation n 0 a :=
  J.homotopyClassOperation_eq n 0 a

/-- The same actual relative comparison preserves the negative-one colimit operation. -/
theorem negative_one_comparison (J : H.RelHomotopy K) :
    H.stableOperation (-1) = K.stableOperation (-1) := J.stableOperation_eq (-1)

/-- A supplied contraction, not an assumed filler existence, kills the original stable operation. -/
theorem supplied_contraction_zero (J : H.RelHomotopy (Homotopy.refl f)) (d : ℤ) :
    H.stableOperation d = 0 :=
  (J.stableOperation_eq d).trans (Homotopy.stableOperation_refl d)

end QuillenTest.SelfTrackRelativeHomotopy
