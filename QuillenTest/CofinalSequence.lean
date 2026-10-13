/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
import Quillen.Topology.ClassifyingSpace.CofinalSequence

/-! QuillenTest for actual contractions induced by cofinal sequences. -/
universe u v
noncomputable section

open CategoryTheory Quillen

example {C : Type u} [Category.{v} C] [Quiver.IsThin C]
    (F : ℕ ⥤ C) (h : ∀ c, ∃ n, Nonempty (c ⟶ F.obj n)) :
    ContractibleSpace (ClassifyingSpace C) :=
  CofinalSequence.contractibleSpace F h

example : ContractibleSpace (ClassifyingSpace ℕ) :=
  CofinalSequence.contractibleSpace (𝟭 ℕ) (fun n => ⟨n, ⟨𝟙 n⟩⟩)

example {C : Type u} [Category.{v} C] [Quiver.IsThin C]
    (F : ℕ ⥤ C) (h : ∀ c, ∃ n, Nonempty (c ⟶ F.obj n)) :
    (ContinuousMap.id (ClassifyingSpace C)).Homotopy
      (ContinuousMap.const _ (classifyingSpacePoint (F.obj 0))) :=
  CofinalSequence.contraction F h
