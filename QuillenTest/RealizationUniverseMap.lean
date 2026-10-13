/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Quillen.Topology.ClassifyingSpace.UniverseLift

/-! Regression tests for actual nerve realizations in genuinely different universes. -/

noncomputable section
open CategoryTheory
open scoped Simplicial Topology
universe u v

example (C : Type u) [Category.{v} C] (c : C) :
    Quillen.classifyingSpaceUniverseHomeomorph.{u, v, max u v + 1} C
      (Quillen.classifyingSpacePoint c) =
        Quillen.classifyingSpacePoint (AsSmall.up.obj c) := by
  simp

example (C : Type u) [Category.{v} C] (x : Quillen.ClassifyingSpace C) :
    Quillen.classifyingSpaceMapUniversal
      (AsSmall.down : AsSmall.{max u v + 1} C ⥤ C)
      (Quillen.classifyingSpaceMapUniversal AsSmall.up x) = x :=
  (Quillen.classifyingSpaceUniverseHomeomorph.{u, v, max u v + 1} C).left_inv x

example {C : Type u} [Category.{v} C]
    {D : Type (u + 1)} [Category.{v + 1} D]
    {E : Type (u + 2)} [Category.{v + 2} E] (F : C ⥤ D) (G : D ⥤ E)
    (x : Quillen.ClassifyingSpace C) :
    Quillen.classifyingSpaceMapUniversal (F ⋙ G) x =
      Quillen.classifyingSpaceMapUniversal G (Quillen.classifyingSpaceMapUniversal F x) := by
  rw [Quillen.classifyingSpaceMapUniversal_comp]
  rfl
