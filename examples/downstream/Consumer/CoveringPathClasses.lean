/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Quillen.Topology.Covering.PathClasses

/-! Independent clients retaining actual covering fibers and projection-square tracks. -/

open Quillen

universe u v w z

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
variable {p : E → B} (hp : IsCoveringMap p)

-- Recovering a path class after fiber transport is actual postcomposition.
example [SimplyConnectedSpace E] (e₀ : E) {x y : B}
    (e : {e : E // p e = x}) (q : Path.Homotopic.Quotient x y) :
    (Covering.pathClassEquiv hp e₀ y).symm (hp.monodromy q e) =
      ((Covering.pathClassEquiv hp e₀ x).symm e).trans q := by
  apply (Covering.pathClassEquiv hp e₀ y).injective
  rw [Equiv.apply_symm_apply, Covering.pathClassEquiv_trans, Equiv.apply_symm_apply]

-- A square with different total/base universes preserves the actual lifted endpoint.
example {E' : Type w} {B' : Type z} [TopologicalSpace E'] [TopologicalSpace B']
    {p' : E' → B'} (hp' : IsCoveringMap p') (k : C(E, E')) (f : C(B, B'))
    (h : ∀ e, p' (k e) = f (p e)) (e₀ : E) {x : B}
    (q : Path.Homotopic.Quotient (p e₀) x) :
    (hp'.monodromy ((q.map f).cast (h e₀) rfl) ⟨k e₀, rfl⟩).1 =
      k (hp.monodromy q ⟨e₀, rfl⟩).1 :=
  Covering.monodromy_naturality_basepoint hp hp' k f h e₀ q
