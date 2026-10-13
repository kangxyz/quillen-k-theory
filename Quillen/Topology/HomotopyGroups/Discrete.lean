/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.HomotopyGroups.Map
public import Mathlib.Topology.Connected.TotallyDisconnected

/-!
# Actual positive homotopy groups of discrete spaces

Continuous positive-dimensional cubes are literally constant; the original
based homotopy quotient therefore has one element in every positive degree.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe u v
namespace Quillen

/-- Positive-dimensional cubes in a discrete space are the actual constant loops. -/
theorem genLoop_eq_const_of_discrete {X : Type u} [TopologicalSpace X]
    [DiscreteTopology X] (x : X) (n : ℕ) (p : GenLoop (Fin (n + 1)) X x) :
    p = GenLoop.const := by
  apply GenLoop.ext
  intro z
  exact (PreconnectedSpace.constant inferInstance p.val.continuous
    (x := z) (y := fun _ ↦ 0)).trans (p.property _ ⟨0, Or.inl rfl⟩)

/-- Discrete spaces have trivial original homotopy groups in every positive degree. -/
theorem subsingleton_positive_pi_of_discrete {X : Type u} [TopologicalSpace X]
    [DiscreteTopology X] (x : X) (n : ℕ) :
    Subsingleton (HomotopyGroup.Pi (n + 1) X x) := by
  refine ⟨?_⟩
  intro a b
  induction a using Quotient.inductionOn with | _ a =>
    induction b using Quotient.inductionOn with | _ b =>
      rw [genLoop_eq_const_of_discrete x n a, genLoop_eq_const_of_discrete x n b]

end Quillen
