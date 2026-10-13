/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Quillen.Topology.Realization.Whitehead

/-! # Original maps, actual inverse homotopies, and the empty cube boundary -/

noncomputable section

open CategoryTheory Quillen
open scoped Simplicial Topology unitInterval

universe u

-- The construction includes dimension zero, with genuinely empty boundary.
example (x : Fin 0 → I) : Quillen.Cube.simplexHomeomorph 0 x ∉ simplexBoundary 0 := by
  rw [Quillen.Cube.simplexHomeomorph_mem_boundary_iff]
  rintro ⟨i, _⟩
  exact Fin.elim0 i

-- An original cube endpoint remains on the actual barycentric boundary.
example (n : ℕ) (x : Fin (n + 1) → I) (hx : x 0 = 0) :
    Quillen.Cube.simplexHomeomorph (n + 1) x ∈ simplexBoundary (n + 1) :=
  (Quillen.Cube.simplexHomeomorph_mem_boundary_iff (n + 1) x).mpr ⟨0, Or.inl hx⟩

-- Both inverse homotopies concern the unchanged original map.
example {X Y : SSet.{u}} (f : C(|X|, |Y|)) (hf : IsWeakHomotopyEquivalence f) :
    ∃ g : C(|Y|, |X|), Nonempty ((g.comp f).Homotopy (ContinuousMap.id |X|)) ∧
      Nonempty ((f.comp g).Homotopy (ContinuousMap.id |Y|)) := by
  let e := Realization.homotopyEquivOfWeakHomotopyEquivalence f hf
  exact ⟨e.invFun, e.left_inv, e.right_inv⟩

example {X Y : SSet.{u}} (f : C(|X|, |Y|)) (hf : IsWeakHomotopyEquivalence f) :
    (Realization.homotopyEquivOfWeakHomotopyEquivalence f hf).toFun = f := rfl
