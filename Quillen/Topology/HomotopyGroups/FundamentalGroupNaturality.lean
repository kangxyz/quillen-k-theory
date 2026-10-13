/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.HomotopyGroups.Map
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

/-! # Naturality of the genuine first homotopy-group comparison -/
@[expose] public section
noncomputable section
universe u₁ u₂
namespace Quillen
/-- The genuine first homotopy-group comparison preserves based continuous maps. -/
theorem piOneEquivFundamentalGroup_naturality
    {X : Type u₁} [TopologicalSpace X] {Y : Type u₂} [TopologicalSpace Y]
    {x : X} {y : Y} (f : C(X, Y)) (h : f x = y) (a : HomotopyGroup.Pi 1 X x) :
    HomotopyGroup.pi1MulEquivFundamentalGroup (piMap 0 f h a) =
      FundamentalGroup.mapOfEq f h (HomotopyGroup.pi1MulEquivFundamentalGroup a) := by
  induction a using Quotient.inductionOn with | _ p =>
    rw [FundamentalGroup.mapOfEq_apply]
    change (⟦genLoopEquivOfUnique (Fin 1) (genLoopPostcomp f h p)⟧ :
        FundamentalGroup Y y) =
      ⟦((genLoopEquivOfUnique (Fin 1) p).map f.continuous).cast h.symm h.symm⟧
    rfl

end Quillen
