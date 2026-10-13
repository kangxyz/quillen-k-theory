/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.HomotopyFiber.WeakCriterion
public import Quillen.Topology.HomotopyFiber.Equivalence
public import Quillen.Topology.HomotopyGroups.Contractible

/-!
# Complete weak equivalences and the actual path-space fibers

Weakness of the actual fiber-to-point maps detects the original total map.
Unbased homotopies preserve complete weak equivalence by explicit path-space
fiber equivalences. Both statements retain nonemptiness and degree zero.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open scoped Topology Simplicial unitInterval
universe u v w
namespace Quillen

/-- Weakness of every actual homotopy fiber's map to a point detects the
original total map, retaining nonemptiness and the zeroth homotopy set. -/
theorem isWeakHomotopyEquivalence_of_fiber_toPoint
    {E B : Type u} [TopologicalSpace E] [TopologicalSpace B] (f : C(E, B))
    (h : ∀ b, IsWeakHomotopyEquivalence
      (ContinuousMap.const (HomotopyFiber f b) (PUnit.unit : PUnit.{u + 1}))) :
    IsWeakHomotopyEquivalence f := by
  apply HomotopyFiber.isWeakHomotopyEquivalence_of_fibers f
  · intro b
    obtain ⟨x, _⟩ := (h b).component_surjective PUnit.unit
    exact ⟨x⟩
  · intro b x n
    let : Subsingleton (HomotopyGroup.Pi n PUnit.{u + 1} PUnit.unit) :=
      subsingleton_pi_of_contractible n _ _
    exact ((h b).homotopy_bijective x n).injective.subsingleton

/-- Unbased homotopies preserve complete weak equivalence of the actual maps.
The fiber comparison includes its actual path concatenation and its inverse. -/
theorem IsWeakHomotopyEquivalence.of_homotopy
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (hf : IsWeakHomotopyEquivalence f) (H : f.Homotopy g) :
    IsWeakHomotopyEquivalence g := by
  apply HomotopyFiber.isWeakHomotopyEquivalence_of_fibers g
  · intro y
    let z := Classical.choice (HomotopyFiber.nonempty_of_weakEquivalence f hf y)
    exact ⟨(HomotopyFiber.homotopyEquiv H y).toFun z⟩
  · intro y z n
    let e := (HomotopyFiber.homotopyEquiv H y).symm
    let := HomotopyFiber.subsingleton_of_weakEquivalence f hf y (e.toFun z) n
    exact (homotopyGroupMap_bijective_of_homotopyEquiv e
      (x := z) (y := e.toFun z) rfl n).injective.subsingleton

end Quillen
