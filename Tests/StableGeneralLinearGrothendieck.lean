/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module
import Quillen.Topology.ClassifyingSpace.StableGeneralLinearGrothendieck

/-! Tests for the original finite-rank Grothendieck projection and its homotopy equivalence. -/
universe u
noncomputable section
open CategoryTheory Quillen Quillen.StableGeneralLinear
open Quillen.StableGeneralLinear.GrothendieckModel

example (R : Type u) [Ring R] :
    ContractibleSpace (ClassifyingSpace (GrothendieckModel.Comma R)) := comma_contractible R

example (R : Type u) [Ring R] :
    (classifyingHomotopyEquiv R).toFun = (classifyingSpaceMap (projection R)).hom := rfl

example (R : Type u) [Ring R] (n : ℕ) :
    CategoryTheory.Grothendieck.ι (categoryDiagram R) (rankIndex n) ⋙ projection R =
      smallFunctor (of R n) := inclusion_projection R n

example : ContractibleSpace (ClassifyingSpace (GrothendieckModel.Comma (ZMod 1))) :=
  comma_contractible (ZMod 1)
