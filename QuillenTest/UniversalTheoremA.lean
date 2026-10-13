/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Quillen.CategoryTheory.TheoremA.UniverseLift

/-! Regression tests for Theorem A and adjunctions with unequal category universes. -/

noncomputable section
open CategoryTheory
open scoped Topology
universe u v

example {C : Type u} [Category.{v} C] {D : Type (u + 1)} [Category.{v + 1} D]
    (F : C ⥤ D)
    (h : ∀ d : D, ContractibleSpace (Quillen.ClassifyingSpace (CostructuredArrow F d)))
    (c : C) :
    Quillen.TheoremA.contractibleCommaClassifyingHomotopyEquivUniversal F h
      (Quillen.classifyingSpacePoint c) = Quillen.classifyingSpacePoint (F.obj c) := by
  change (Quillen.TheoremA.contractibleCommaClassifyingHomotopyEquivUniversal F h).toFun
    (Quillen.classifyingSpacePoint c) = _
  rw [Quillen.TheoremA.contractibleCommaClassifyingHomotopyEquivUniversal_toFun]
  exact Quillen.classifyingSpaceMapUniversal_point F c

example {C : Type u} [Category.{v} C] {D : Type (u + 1)} [Category.{v + 1} D]
    {F : C ⥤ D} {G : D ⥤ C} (a : F ⊣ G)
    [ContractibleSpace (Quillen.ClassifyingSpace D)] :
    ContractibleSpace (Quillen.ClassifyingSpace C) :=
  (Quillen.adjunctionClassifyingHomotopyEquivUniversal a).contractibleSpace

example {C : Type u} [Category.{v} C] {D : Type (u + 1)} [Category.{v + 1} D]
    {F G : C ⥤ D} (α : F ⟶ G) (x : Quillen.ClassifyingSpace C) :
    Quillen.classifyingSpaceUniversalHomotopy α (0, x) =
      Quillen.classifyingSpaceMapUniversal F x :=
  (Quillen.classifyingSpaceUniversalHomotopy α).map_zero_left x
