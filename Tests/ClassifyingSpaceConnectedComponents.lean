/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
import Quillen.Topology.ClassifyingSpace.ConnectedComponents
/-! Original component inclusions and their actual path-component topology. -/
noncomputable section
open CategoryTheory Quillen
universe u
example (C : Type u) [Category.{u} C] (b : C) :
    ClassifyingSpace (CategoryTheory.ConnectedComponents.mk b).Component ≃ₜ
      pathComponent (classifyingSpacePoint b) :=
  classifyingSpaceComponentHomeomorph C b
example (C : Type u) [Category.{u} C] (b : C)
    (x : ClassifyingSpace (CategoryTheory.ConnectedComponents.mk b).Component) :
    (classifyingSpaceComponentHomeomorph C b x).val =
      classifyingSpaceMap (CategoryTheory.ConnectedComponents.ι _) x := rfl
