/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Topology.FilteredRealization.CompactHELP
public import Quillen.Topology.HELP.CompactHomotopyEquivalence

/-!
# Actual homotopy invariance of filtered simplicial colimits

Every canonical stage-to-colimit realization map is an actual homotopy
equivalence when every realized transition is one. Compact finite support
and exact homotopy-square lifting give compact HELP; lifting over realized
simplicial inclusions then constructs both global inverse homotopies.
No countability assumption or Whitehead theorem is used.
-/
@[expose] public section

noncomputable section
open CategoryTheory Limits
open scoped Simplicial
universe u

namespace Quillen.FilteredRealization
variable {J : Type u} [SmallCategory J] [IsFiltered J]
  (F : J ⥤ SSet.{u}) (c : Cocone F) (hc : IsColimit c)

/-- Actual canonical filtered-colimit invariance. The transition inverses
need not be coherent or preserve any chosen basepoint. -/
def stageHomotopyEquiv
    (e : ∀ {j k : J} (u : j ⟶ k), ContinuousMap.HomotopyEquiv |F.obj j| |F.obj k|)
    (he : ∀ {j k : J} (u : j ⟶ k), (e u).toFun = (SSet.toTop.map (F.map u)).hom)
    (j : J) : ContinuousMap.HomotopyEquiv |F.obj j| |c.pt| :=
  homotopyEquivOfCompactHELP (SSet.toTop.map (c.ι.app j)).hom
    (stage_compactHELP F c hc e he j)

@[simp]
theorem stageHomotopyEquiv_toFun
    (e : ∀ {j k : J} (u : j ⟶ k), ContinuousMap.HomotopyEquiv |F.obj j| |F.obj k|)
    (he : ∀ {j k : J} (u : j ⟶ k), (e u).toFun = (SSet.toTop.map (F.map u)).hom)
    (j : J) : (stageHomotopyEquiv F c hc e he j).toFun =
      (SSet.toTop.map (c.ι.app j)).hom := rfl

end Quillen.FilteredRealization
