/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.ClassifyingSpace.GrothendieckWeakBase
public import Quillen.Topology.ClassifyingSpace.EndofunctorIterationHomotopy
public import Quillen.Topology.ClassifyingSpace.Equivalence
public import Mathlib.CategoryTheory.Limits.Preorder

/-! # Original stage inclusions for a telescope of homotopy equivalences -/

@[expose] public section
noncomputable section
open CategoryTheory
universe u v
namespace Quillen.EndofunctorTelescope
variable {C : Type u} [Category.{v} C] (T : C ⥤ C)

/-- Each original stage is a weak equivalence when the original single step is
realized by the specified homotopy equivalence. The base contraction is the one
provided by the actual initial natural-number stage. -/
theorem stageInclusion_isWeakHomotopyEquivalence
    (e : ContinuousMap.HomotopyEquiv (ClassifyingSpace C) (ClassifyingSpace C))
    (he : e.toFun = classifyingSpaceMapUniversal T) (n : ℕ) :
    IsWeakHomotopyEquivalence (classifyingSpaceMapUniversal (Grothendieck.ι (diagram T) n)) := by
  let : ContractibleSpace (ClassifyingSpace ℕ) :=
    classifyingSpace_contractible_of_isInitial (Limits.isInitialBot (α := ℕ))
  obtain ⟨b⟩ := ContractibleSpace.hequiv (ClassifyingSpace ℕ) PUnit.{1}
  have hb : b.toFun = ContinuousMap.const _ (PUnit.unit : PUnit.{1}) := by ext x
  have hbase := isWeakHomotopyEquivalence_of_homotopyEquiv b
  rw [hb] at hbase
  exact GrothendieckForget.fiberInclusion_isWeakHomotopyEquivalence (diagram T)
    (fun {i j} _ ↦ iterateClassifyingHomotopyEquiv e (j - i))
    (fun {i j} _ ↦ iterateClassifyingHomotopyEquiv_toFun T e he (j - i)) hbase n

end Quillen.EndofunctorTelescope
