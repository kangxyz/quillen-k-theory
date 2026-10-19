/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveFiniteParameter

/-!
# Full-node naturality of the finite parameter family

A commuting square of the actual dependent node functions gives a literal equality of
whole realized parameter families. The finite simplex coordinate is unchanged. This is
an equality of scalar carrier maps, rather than an inference from native evaluation.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory Convexity
open scoped Simplicial Topology
universe u

namespace Quillen.Waldhausen.IteratedS.CommonReferenceNerve.FiniteParameter

variable {V W V' W' U T U' T' : Model.{u}}
  {E : V ⟶ W} {E' : V' ⟶ W'} {F : U ⟶ T} {F' : U' ⟶ T'}
  {q : ℕ}

/-- A full dependent-node square commutes on every point of the whole source nerve. -/
theorem parameter_naturality
    (a : Node E → Node E') (b : Node F → Node F')
    (f : Node E → Fin (q + 1) → Node F) (f' : Node E' → Fin (q + 1) → Node F')
    (h : ∀ e j, b (f e j) = f' (a e) j)
    (x : |nerve (Codiscrete (Node E))|) (w : StdSimplex ℝ (Fin (q + 1))) :
    mapParameter b (parameter E F f (x, w)) =
      parameter E' F' f' (mapParameter a x, w) := by
  obtain ⟨p, N, z, rfl⟩ := exists_parameter E x
  rw [parameter_characteristic, mapParameter_parameter, mapParameter_parameter,
    parameter_characteristic]
  apply congrArg (fun M ↦ CommonReferenceNerve.parameter F' M
    (SimplexGrid.parameter.{u} p q (z, w)))
  funext i
  exact h _ _

end Quillen.Waldhausen.IteratedS.CommonReferenceNerve.FiniteParameter
