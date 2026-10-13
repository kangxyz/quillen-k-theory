/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Prespectrum.TelescopeMovingBasepoint
public import Quillen.Topology.Prespectrum.LoopTailReplacement

/-!
# Original-map consumers of moving-basepoint telescope representability

The consumers retain an original cylinder height and stage point, a possibly nonconstant loop
component of the actual loop-tail replacement, and whole boundary-relative nullhomotopies at
arbitrary stage points. The structure comparison keeps contraction time and loop time separate.
No complete weak-equivalence or Omega-spectrum conclusion is inferred.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Quillen Quillen.LoopPrespectrum
open scoped Topology unitInterval

universe u

namespace QuillenTest.TelescopeMovingBasepoint

open Quillen

variable (E : ℕ → LoopPrespectrum.{u}) (f : ∀ i, E i ⟶ E (i + 1)) (k : ℕ)

/-- An actual cylinder point, including its original height, has a finite-stage class
representative under the two displayed original tracks. -/
theorem original_cylinder_class_lifts [∀ i, T1Space ((E i).space k)]
    (i : ℕ) (s : unitInterval) (x : (E i).space k) (n : ℕ)
    (a : HomotopyGroup.Pi n (Telescope.Space E f k) (Telescope.cylinder E f k i (s, x))) :
    ∃ N : ℕ, ∃ hi : i ≤ N,
      ∃ b : HomotopyGroup.Pi n ((E N).space k) ((Telescope.transition E f i N hi).map k x),
        pathTransport (Telescope.stageTransitionPath E f hi k x) n
          (pathTransport (Telescope.cylinderStagePath E f k i s x) n a) =
            homotopyGroupMap ((Telescope.inclusion E f N).map k) rfl b :=
  Telescope.exists_homotopyGroup_representative_at E f k i x n
    (pathTransport (Telescope.cylinderStagePath E f k i s x) n a)

/-- A nullhomotopy at an arbitrary original stage point becomes an actual based nullhomotopy
of the unchanged finite transition, without a chosen-component restriction. -/
theorem original_stage_nullhomotopy_detected [∀ i, T1Space ((E i).space k)]
    (i : ℕ) (x : (E i).space k) (n : ℕ) (p : GenLoop (Fin n) ((E i).space k) x)
    (H : GenLoop.Homotopic
      (genLoopPostcomp ((Telescope.inclusion E f i).map k) rfl p) GenLoop.const) :
    ∃ N : ℕ, ∃ hi : i ≤ N,
      GenLoop.Homotopic
        (genLoopPostcomp ((Telescope.transition E f i N hi).map k) rfl p) GenLoop.const := by
  have h : homotopyGroupMap ((Telescope.inclusion E f i).map k) rfl (Quotient.mk' p) =
      homotopyGroupMap ((Telescope.inclusion E f i).map k) rfl
        (Quotient.mk' (GenLoop.const (N := Fin n) (x := x))) := by
    change Quotient.mk' (genLoopPostcomp ((Telescope.inclusion E f i).map k) rfl p) =
      Quotient.mk' (genLoopPostcomp ((Telescope.inclusion E f i).map k) rfl GenLoop.const)
    rw [genLoopPostcomp_const]
    exact Quotient.sound H
  obtain ⟨N, hi, hN⟩ := Telescope.exists_eventual_homotopyGroup_eq_at E f k i x n _ _ h
  change Quotient.mk' (genLoopPostcomp ((Telescope.transition E f i N hi).map k) rfl p) =
    Quotient.mk' (genLoopPostcomp ((Telescope.transition E f i N hi).map k) rfl GenLoop.const) at hN
  rw [genLoopPostcomp_const] at hN
  exact ⟨N, hi, Quotient.exact hN⟩

/-- The original finite-stage basepoint track preserves both independent parameters. -/
theorem original_stage_structure_track {i N : ℕ} (hi : i ≤ N)
    (x : (E i).space k) (s t : unitInterval) :
    Telescope.stageTransitionPath E f hi (k + 1) ((E i).structureMap k x t) s =
      (Telescope.prespectrum E f).structureMap k
        (Telescope.stageTransitionPath E f hi k x s) t :=
  Telescope.stageTransitionPath_structure E f hi k x s t

/-- The first actual loop-tail stage retains a possibly nonconstant original loop as its
basepoint; every class there has the proved finite-stage representative with its exact track. -/
theorem original_loop_component_class_lifts (F : LoopPrespectrum.{u})
    [∀ j, T1Space (F.space j)] (k n : ℕ)
    (γ : Path (F.point (k + 1)) (F.point (k + 1)))
    (a : HomotopyGroup.Pi n ((loopTailReplacement F).space k)
      ((Telescope.inclusion (loopTailIterate F) (loopTailTransition F) 1).map k γ)) :
    ∃ N : ℕ, ∃ hi : 1 ≤ N,
      ∃ b : HomotopyGroup.Pi n ((loopTailIterate F N).space k)
        ((Telescope.transition (loopTailIterate F) (loopTailTransition F) 1 N hi).map k γ),
        pathTransport
          (Telescope.stageTransitionPath (loopTailIterate F) (loopTailTransition F) hi k γ) n a =
            homotopyGroupMap
              ((Telescope.inclusion (loopTailIterate F) (loopTailTransition F) N).map k) rfl b :=
  Telescope.exists_homotopyGroup_representative_at (loopTailIterate F) (loopTailTransition F)
    k 1 γ n a

end QuillenTest.TelescopeMovingBasepoint
