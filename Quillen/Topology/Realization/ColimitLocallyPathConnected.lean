/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import Mathlib.Topology.Connected.LocallyPathConnected

/-!
# Local path connectedness of actual topological colimits

The argument uses the actual final topology,
not an equivalence of homotopy types. It says nothing about semilocal simple
connectivity, which does not follow from this colimit argument.
-/

@[expose] public section
open CategoryTheory CategoryTheory.Limits Set Topology
universe u v w
namespace Quillen

variable {J : Type v} [Category.{w} J] (F : J ⥤ TopCat.{u})

/-- Every pathcomponent of an open subset of an actual topological colimit is
open when all the diagram objects are locally path connected. -/
theorem locallyPathConnectedSpace_of_isColimit
    [∀ j, LocallyPathConnectedSpace (F.obj j)]
    (c : Cocone F) (hc : IsColimit c) : LocallyPathConnectedSpace c.pt := by
  apply locallyPathConnectedSpace_iff_isOpen_pathComponentIn.mpr
  intro x U hU
  rw [TopCat.isOpen_iff_of_isColimit c hc]
  intro j
  apply isOpen_iff_mem_nhds.mpr
  intro z hz
  change JoinedIn U x ((c.ι.app j) z) at hz
  let V : Set (F.obj j) := c.ι.app j ⁻¹' U
  have hV : IsOpen V := hU.preimage (c.ι.app j).hom.continuous
  have hzV : z ∈ V := hz.target_mem
  refine mem_nhds_iff.mpr ⟨pathComponentIn V z, ?_,
    hV.pathComponentIn z, mem_pathComponentIn_self hzV⟩
  intro y hy
  have hzy : JoinedIn V z y := hy
  exact hz.trans ⟨hzy.somePath.map (c.ι.app j).hom.continuous,
    fun t => hzy.somePath_mem t⟩

end Quillen
