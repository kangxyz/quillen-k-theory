/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Quillen.Topology.CWComplex.Whitehead

/-! # Independent clients of actual classical-CW Whitehead -/
@[expose] public section

open Topology

open Quillen.ClassicalCW

noncomputable section
open Set
universe u
namespace Quillen.Consumer.ClassicalCWWhitehead
open ClassicalCW
variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
variable [T2Space X] [T2Space Y]
variable (C : Set X) (D : Set Y) [CWComplex C] [CWComplex D]

/-- The unchanged original weak map admits an actual continuous two-sided inverse
up to homotopy, with no realization, covering or compact-HELP input. -/
theorem originalMapHasInverse (f : C(C, D)) (hf : IsWeakHomotopyEquivalence f) :
    ∃ g : C(D, C), (g.comp f).Homotopic (ContinuousMap.id C) ∧
      (f.comp g).Homotopic (ContinuousMap.id D) :=
  ⟨weakMapInverse C D f hf, ⟨weakMapLeftHomotopy C D f hf⟩,
    ⟨weakMapRightHomotopy C D f hf⟩⟩

/-- The actual map criterion is an equivalence, not merely a statement that
some unrelated homotopy equivalence exists between the same spaces. -/
theorem exactForwardRecognition (f : C(C, D)) :
    IsWeakHomotopyEquivalence f ↔ ∃ e : ContinuousMap.HomotopyEquiv C D, e.toFun = f :=
  isWeakHomotopyEquivalence_iff_exists_homotopyEquiv C D f

end Quillen.Consumer.ClassicalCWWhitehead
