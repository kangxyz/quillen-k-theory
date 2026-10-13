/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Quillen.Topology.ClassifyingSpace.ConnectedComponents

/-! # Actual path components of a category's classifying space -/
@[expose] public section
noncomputable section
open CategoryTheory
universe u
namespace Quillen
variable (C : Type u) [Category.{u} C]

/-- The categorical component index of an actual realization point. -/
def classifyingSpaceComponentIndex (x : ClassifyingSpace C) :
    CategoryTheory.ConnectedComponents C :=
  ((classifyingSpaceComponentSigmaHomeomorph C).symm x).1

/-- Each original object vertex retains its categorical connected component. -/
theorem classifyingSpaceComponentIndex_point (b : C) :
    classifyingSpaceComponentIndex C (classifyingSpacePoint b) =
      CategoryTheory.ConnectedComponents.mk b := by
  let v : (CategoryTheory.ConnectedComponents.mk b).Component := ⟨b, rfl⟩
  have h : classifyingSpaceComponentSigmaHomeomorph C
      ⟨CategoryTheory.ConnectedComponents.mk b, classifyingSpacePoint v⟩ =
        classifyingSpacePoint b := by simp [v]
  rw [classifyingSpaceComponentIndex, ← h, Homeomorph.symm_apply_apply]

/-- Equality of the categorical indices is exactly being joined in the actual realization. -/
theorem classifyingSpaceComponentIndex_eq_iff (x y : ClassifyingSpace C) :
    classifyingSpaceComponentIndex C x = classifyingSpaceComponentIndex C y ↔ Joined x y := by
  let e := classifyingSpaceComponentSigmaHomeomorph C
  constructor
  · intro h
    obtain ⟨a, ha⟩ := e.surjective x
    obtain ⟨b, hb⟩ := e.surjective y
    subst x
    subst y
    change (e.symm (e a)).1 = (e.symm (e b)).1 at h
    simp only [e.symm_apply_apply] at h
    rcases a with ⟨c, a⟩
    rcases b with ⟨d, b⟩
    dsimp only at h
    subst d
    exact ((PathConnectedSpace.joined a b).map
      (continuous_sigmaMk (i := c))).map e.continuous
  · intro h
    exact classifyingSpace_sigma_joined_index C _ _ (h.map e.symm.continuous)

/-- The genuine quotient map from topological to categorical components. -/
def classifyingSpaceZerothHomotopyToComponents :
    ZerothHomotopy (ClassifyingSpace C) → CategoryTheory.ConnectedComponents C :=
  ZerothHomotopy.lift (classifyingSpaceComponentIndex C)
    (fun _ _ p ↦ (classifyingSpaceComponentIndex_eq_iff C _ _).mpr ⟨p⟩)

/-- The original topological quotient has precisely the categorical component indices. -/
theorem classifyingSpaceZerothHomotopyToComponents_bijective :
    Function.Bijective (classifyingSpaceZerothHomotopyToComponents C) := by
  constructor
  · intro a b h
    obtain ⟨x, rfl⟩ := ZerothHomotopy.mk_surjective a
    obtain ⟨y, rfl⟩ := ZerothHomotopy.mk_surjective b
    exact Quotient.sound ((classifyingSpaceComponentIndex_eq_iff C x y).mp h)
  · intro c
    obtain ⟨b, rfl⟩ := Quotient.exists_rep c
    exact ⟨ZerothHomotopy.mk (classifyingSpacePoint b),
      classifyingSpaceComponentIndex_point C b⟩

/-- The actual path-component quotient of the classifying space equals categorical components. -/
def classifyingSpaceZerothHomotopyEquiv :
    ZerothHomotopy (ClassifyingSpace C) ≃ CategoryTheory.ConnectedComponents C :=
  Equiv.ofBijective (classifyingSpaceZerothHomotopyToComponents C)
    (classifyingSpaceZerothHomotopyToComponents_bijective C)

/-- The equivalence preserves every original object vertex, with no chosen representative change. -/
theorem classifyingSpaceZerothHomotopyEquiv_point (b : C) :
    classifyingSpaceZerothHomotopyEquiv C (ZerothHomotopy.mk (classifyingSpacePoint b)) =
      CategoryTheory.ConnectedComponents.mk b :=
  classifyingSpaceComponentIndex_point C b

/-- The inverse equivalence takes an object's categorical class to its original vertex class. -/
theorem classifyingSpaceZerothHomotopyEquiv_symm_mk (b : C) :
    (classifyingSpaceZerothHomotopyEquiv C).symm
        (CategoryTheory.ConnectedComponents.mk b) =
      ZerothHomotopy.mk (classifyingSpacePoint b) :=
  (classifyingSpaceZerothHomotopyEquiv C).symm_apply_eq.mpr
    (classifyingSpaceZerothHomotopyEquiv_point C b).symm

/-- Every topological path component contains an original object vertex. -/
theorem classifyingSpaceVertexComponent_surjective :
    Function.Surjective (fun b : C ↦ ZerothHomotopy.mk (classifyingSpacePoint b)) := by
  intro a
  obtain ⟨b, hb⟩ := Quotient.exists_rep (classifyingSpaceZerothHomotopyEquiv C a)
  refine ⟨b, (classifyingSpaceZerothHomotopyEquiv C).injective ?_⟩
  exact (classifyingSpaceZerothHomotopyEquiv_point C b).trans hb

end Quillen
