/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Quillen.Topology.ClassifyingSpace.ExtensionTotal
import Quillen.Algebra.Category.ModuleCat.FiniteProjective

/-! Consumers retaining the exact total category and the specified contraction vertex. -/

noncomputable section

open CategoryTheory CategoryTheory.Limits Quillen

universe u v

example {C : Type u} [Category.{v} C] {z : C} (hz : IsInitial z) :
    ContractibleSpace (ClassifyingSpace (Subdivision C)) :=
  Subdivision.contractibleSpace_of_isInitial hz

example {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
    (E : ExactStructure C) :
    (ContinuousMap.id (ClassifyingSpace E.ExtensionTotal)).Homotopy
      (ContinuousMap.const _ (classifyingSpacePoint E.extensionTotalPoint)) :=
  E.extensionTotalContraction

example (R : Type u) [Ring R] :
    ContractibleSpace
      (ClassifyingSpace (FiniteProjectiveModule.exactStructure Rᵐᵒᵖ).ExtensionTotal) :=
  (FiniteProjectiveModule.exactStructure Rᵐᵒᵖ).extensionTotal_contractibleSpace
