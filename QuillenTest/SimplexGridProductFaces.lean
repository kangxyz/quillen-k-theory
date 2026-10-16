/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Realization.SimplexGridProductFaces

/-! A strict client of the genuine product-realization face equation, at arbitrary dimensions. -/

public section
noncomputable section
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
open CategoryTheory Convexity
open scoped Simplicial Topology
universe u
namespace QuillenTest.SimplexGridProductFaces
open Quillen.SimplexGrid

/-- Both independent simplex coordinates retain the exact supplied ordered product face. -/
theorem original_product_face {p q p' q' : ℕ}
    (α : ⦋p⦌ ⟶ ⦋p'⦌) (β : ⦋q⦌ ⟶ ⦋q'⦌)
    (γ : ⦋dimension p q⦌ ⟶ ⦋dimension p' q'⦌)
    (hγ : ∀ i j, γ.toOrderHom (index p q (i, j)) =
      index p' q' (α.toOrderHom i, β.toOrderHom j))
    (z : StdSimplex ℝ (Fin (p + 1))) (w : StdSimplex ℝ (Fin (q + 1))) :
    parameter.{u} p' q' (StdSimplex.map α.toOrderHom z, StdSimplex.map β.toOrderHom w) =
      StdSimplex.map γ.toOrderHom (parameter.{u} p q (z, w)) :=
  parameter_productMap α β γ hγ z w

end QuillenTest.SimplexGridProductFaces
