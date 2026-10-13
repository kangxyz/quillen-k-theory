/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Topology.Realization.Homotopy

/-!
# Realization of constant simplicial maps

The realization of the literal constant simplicial map is the constant map at
its realized vertex. This applies to arbitrary simplicial sets in one universe.
-/
@[expose] public section

noncomputable section

open CategoryTheory Opposite
open scoped Simplicial

universe u

namespace Quillen

/-- A constant simplicial map realizes to the corresponding constant continuous map. -/
theorem realization_const_apply {X Y : SSet.{u}} (y : Y _⦋0⦌) (x : |X|) :
    SSet.toTop.map (SSet.const y : X ⟶ Y) x = realizationPoint y := by
  have hv : (SSet.yonedaEquiv.symm y).app _
      (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋0⦌) : (Δ[0] : SSet.{u}) _⦋0⦌) = y := by
    exact SSet.yonedaEquiv.apply_symm_apply y
  have hc : (SSet.const y : X ⟶ Y) =
      SSet.const (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋0⦌) : (Δ[0] : SSet.{u}) _⦋0⦌) ≫
        SSet.yonedaEquiv.symm y := by
    rw [SSet.const_comp, hv]
  rw [hc, Functor.map_comp]
  change SSet.toTop.map (SSet.yonedaEquiv.symm y) _ = _
  exact congrArg (SSet.toTop.map (SSet.yonedaEquiv.symm y))
    (Subsingleton.elim _ default)

end Quillen
