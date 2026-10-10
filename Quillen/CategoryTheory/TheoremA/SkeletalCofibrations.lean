/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.CategoryTheory.TheoremA.BisimplicialCoproducts
public import Quillen.CategoryTheory.TheoremA.EnrichedBoundaryHEP

/-! # Genuine cofibrations in the realized base-skeleton tower -/
@[expose] public section


noncomputable section

open CategoryTheory Limits Opposite
open scoped Simplicial Topology

universe u

namespace Quillen.TheoremA

variable {D : Type u} [SmallCategory D] (H : D ⥤ SSet.{u})

/-- The realized coproduct of all enriched simplex-boundary inclusions has HEP. -/
theorem homotopyExtensionProperty_replacementCellsBoundary (n : ℕ) :
    homotopyExtensionProperty (SSet.toTop.map (diagonalMap (replacementCellsBoundaryι H n))) :=
  homotopyExtensionProperty_realizedBisimplicialSigma
    (fun s : (nerve D).nonDegenerate n ↦ replacementCellBoundaryι H s)
    (fun s ↦ homotopyExtensionProperty_replacementCellBoundary H s)

/-- Each successor inclusion in the actual realized base-skeleton filtration
has the homotopy extension property. The attachment and boundary HEP are
proved from the real simplicial cells and their topological realizations. -/
theorem homotopyExtensionProperty_realizedReplacementSkeleton_succ (n : ℕ) :
    homotopyExtensionProperty ((realizedReplacementSkeleton H).map (homOfLE (Nat.le_succ n))) :=
  homotopyExtensionProperty_pushout (realizedReplacementSkeleton_isPushout H n).flip
    (homotopyExtensionProperty_replacementCellsBoundary H n)

/-- Every inclusion between finite stages of the actual realized skeletal
tower has HEP. -/
theorem homotopyExtensionProperty_realizedReplacementSkeleton {n m : ℕ} (h : n ≤ m) :
    homotopyExtensionProperty ((realizedReplacementSkeleton H).map (homOfLE h)) := by
  induction m, h using Nat.le_induction with
  | base =>
    simpa using homotopyExtensionProperty_of_isIso (𝟙 ((realizedReplacementSkeleton H).obj n))
  | succ m h ih =>
    have heq : (homOfLE (Nat.le_succ_of_le h)) = homOfLE h ≫ homOfLE (Nat.le_succ m) := rfl
    rw [heq, Functor.map_comp]
    exact homotopyExtensionProperty_comp ih
      (homotopyExtensionProperty_realizedReplacementSkeleton_succ H m)

end Quillen.TheoremA
