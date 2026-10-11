/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Topology.Prespectrum.LoopTailComponentApproximation
public import Quillen.Topology.Prespectrum.Omega

/-!
# The actual loop-tail telescope is an Omega spectrum

For the original levelwise T1 hypothesis, every unchanged structure adjoint of the existing
loop-tail replacement is a complete weak homotopy equivalence. Arbitrary telescope source points
are moved by their original cylinder and finite-transition paths to positive-stage points; the
all-degree theorem there is already proved using compact representatives and eventual equality.
Target component coverage is the previously proved original zero-degree comparison.

Together with the original stable-equivalence initial inclusion, this supplies a genuine
Omega replacement. Cone preservation and general stable cofiber excision are not asserted.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory
open scoped Topology unitInterval

universe u

namespace Quillen.LoopPrespectrum

variable (E : LoopPrespectrum.{u}) [∀ k, T1Space (E.space k)]

/-- The same original structure adjoint is completely weak: all finite groups at every source
point, and actual target component coverage. Only the original levelwise T1 hypothesis is used. -/
theorem loopTailReplacement_structureMap_isWeakHomotopyEquivalence (k : ℕ) :
    IsWeakHomotopyEquivalence ((loopTailReplacement E).structureMap k) where
  component_surjective := loopTailReplacement_structureMap_component_surjective E k
  homotopy_bijective x n := by
    obtain ⟨i, γ, ⟨p⟩⟩ := Telescope.exists_stage_point
      (loopTailIterate E) (loopTailTransition E) k x
    let γ' := (Telescope.transition (loopTailIterate E) (loopTailTransition E)
      i (i + 1) (Nat.le_succ i)).map k γ
    let q := Telescope.stageTransitionPath (loopTailIterate E) (loopTailTransition E)
      (Nat.le_succ i) k γ
    exact (homotopyGroupMap_bijective_iff_of_path ((loopTailReplacement E).structureMap k)
      (p.trans q) n).mpr
        ⟨loopTailReplacement_structureMap_injective_at_stage E i k n γ',
          loopTailReplacement_structureMap_surjective_at_stage E i k n γ'⟩

/-- The existing stable-group-preserving loop-tail telescope is genuinely an Omega spectrum. -/
theorem loopTailReplacement_isOmega : (loopTailReplacement E).IsOmega :=
  loopTailReplacement_structureMap_isWeakHomotopyEquivalence E

end Quillen.LoopPrespectrum
