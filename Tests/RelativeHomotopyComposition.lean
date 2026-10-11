/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Topology.Prespectrum.RelativeHomotopyComposition

/-! Comparison time is reversed or concatenated independently of the other original coordinates. -/
@[expose] public section
noncomputable section
open CategoryTheory Quillen.LoopPrespectrum
open scoped Topology unitInterval
universe u
namespace Quillen.Tests.RelativeHomotopyComposition
variable {E F : LoopPrespectrum.{u}} {f g : E ⟶ F} {H K L : Homotopy f g}

lemma reversed_coordinates (J : H.RelHomotopy K) (n : ℕ) (r s : unitInterval)
    (x : E.space n) :
    J.symm.level n (r, (s, x)) = J.level n (unitInterval.symm r, (s, x)) := rfl

lemma concatenated_independent_structure (J : H.RelHomotopy K) (J' : K.RelHomotopy L)
    (n : ℕ) (r s t : unitInterval) (x : E.space n) :
    (J.trans J').level (n + 1) (r, (s, E.structureMap n x t)) =
      F.structureMap n ((J.trans J').level n (r, (s, x))) t :=
  (J.trans J').comm n r s x t

end Quillen.Tests.RelativeHomotopyComposition
