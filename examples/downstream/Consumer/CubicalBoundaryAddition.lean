/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.HomotopyGroups.CubicalUpperFaceFold

/-! An independent client uses actual concatenation and the terminal relative
homotopy without importing a boundary-addition theorem. -/

@[expose] public section
noncomputable section
open scoped Topology unitInterval
universe u
namespace Quillen.Consumer.CubicalBoundaryAddition
variable {n : ℕ} {Z : Type u} [TopologicalSpace Z] {z : Z}

/-- The lower fold is literal cubical concatenation, independently of quotient algebra. -/
theorem actual_concatenation (F : C((Fin (n + 1) → I), Z))
    (hF : ∀ x ∈ cubeCodimTwoBoundary (Fin (n + 1)), F x = z) (k : Fin n) :
    topGenLoop (foldContinuousCube F 0 k.succ)
      (foldContinuousCube_codimTwo F hF 0 k.succ (Fin.succ_ne_zero k).symm) =
        GenLoop.transAt k (lateralGenLoop F hF k 0 (Or.inl rfl)) (topGenLoop F hF) :=
  topGenLoop_fold_eq_transAt F hF k

/-- A cube with constant lateral faces itself witnesses equality in the original quotient. -/
theorem terminal_quotient_equality (F : C((Fin (n + 1) → I), Z))
    (hF : ∀ x ∈ cubeCodimTwoBoundary (Fin (n + 1)), F x = z)
    (hside : ∀ (k : Fin n) (x : Fin (n + 1) → I),
      x k.succ = 0 ∨ x k.succ = 1 → F x = z) :
    cubicalClass (bottomGenLoop F hF) = cubicalClass (topGenLoop F hF) :=
  Quotient.sound ⟨allSidesConstantHomotopy F hF hside⟩

end Quillen.Consumer.CubicalBoundaryAddition
