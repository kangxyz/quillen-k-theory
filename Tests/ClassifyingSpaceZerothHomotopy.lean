/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module
public import Quillen.Topology.ClassifyingSpace.ZerothHomotopy

/-! # Actual topological/categorical component quotient consumers -/
noncomputable section
open CategoryTheory Quillen
universe u
variable (C : Type u) [Category.{u} C]

example : ZerothHomotopy (ClassifyingSpace C) ≃ CategoryTheory.ConnectedComponents C :=
  classifyingSpaceZerothHomotopyEquiv C

example (b : C) :
    classifyingSpaceZerothHomotopyEquiv C (ZerothHomotopy.mk (classifyingSpacePoint b)) =
      CategoryTheory.ConnectedComponents.mk b :=
  classifyingSpaceZerothHomotopyEquiv_point C b

example (x y : ClassifyingSpace C) :
    classifyingSpaceComponentIndex C x = classifyingSpaceComponentIndex C y ↔ Joined x y :=
  classifyingSpaceComponentIndex_eq_iff C x y

example (a : ZerothHomotopy (ClassifyingSpace C)) :
    ∃ b : C, ZerothHomotopy.mk (classifyingSpacePoint b) = a :=
  classifyingSpaceVertexComponent_surjective C a
