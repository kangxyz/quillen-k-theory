/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Cube.StickBreakingFaces
public import Quillen.Topology.HomotopyGroups.SphericalSimplexQuotient

/-! An independent client uses quotient representatives to detect genuine nullhomotopy. -/

@[expose] public section

open Convexity Quillen
open scoped Topology unitInterval
noncomputable section
universe u

namespace QuillenConsumer.StickBreaking

/-- Every original degree-two class has a controlled representative detecting its vanishing. -/
theorem exists_representative_detecting_vanishing {Z : Type u} [TopologicalSpace Z] {z : Z}
    (a : HomotopyGroup.Pi 2 Z z) :
    ∃ f : SphericalSimplex Z z 2, f.homotopyClassStick = a ∧
      (a = 1 ↔ f.homotopyClass = 1) := by
  obtain ⟨f, rfl⟩ := SphericalSimplex.homotopyClassStick_surjective a
  exact ⟨f, rfl, f.homotopyClassStick_eq_one_iff_chosen⟩

/-- A genuine homotopy of descended simplices identifies the original cubical classes. -/
theorem class_eq_of_descended_homotopy {Z : Type u} [TopologicalSpace Z] {z : Z}
    (p q : GenLoop (Fin 2) Z z)
    (H : (SphericalSimplex.ofGenLoopStick p).val.HomotopyRel
      (SphericalSimplex.ofGenLoopStick q).val (simplexBoundary 2)) :
    (Quotient.mk' p : HomotopyGroup.Pi 2 Z z) = Quotient.mk' q := by
  have h := SphericalSimplex.homotopyToGenLoopStick H
  simp only [SphericalSimplex.toGenLoopStick_ofGenLoopStick] at h
  exact Quotient.sound ⟨h⟩

end QuillenConsumer.StickBreaking
