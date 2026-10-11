/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Topology.Prespectrum.LoopTailOmega

/-!
# Original-map consumers of the genuine loop-tail Omega replacement

Actual target cubes lift and actual source homotopies reflect at every displayed source point,
including arbitrary nonchosen components and degree zero. The original target loop has an actual
component preimage. The literal initial inclusion still lifts every signed stable class, while
the target is now proved Omega. Parameter tests retain the original prefix track and finite loop
transition. None of these consumers infer cone preservation or stable excision.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Quillen Quillen.LoopPrespectrum
open scoped Topology unitInterval

universe u

namespace Quillen.Tests.LoopTailOmega

variable (E : LoopPrespectrum.{u}) [∀ k, T1Space (E.space k)]

/-- Every target cube based at the structure image of any original source point lifts to an
actual source cube with the whole boundary-relative comparison, including degree zero. -/
theorem original_arbitrary_point_target_cube_lifts (k n : ℕ)
    (x : (loopTailReplacement E).space k)
    (p : GenLoop (Fin n)
      (Path ((loopTailReplacement E).point (k + 1)) ((loopTailReplacement E).point (k + 1)))
      ((loopTailReplacement E).structureMap k x)) :
    ∃ q : GenLoop (Fin n) ((loopTailReplacement E).space k) x,
      GenLoop.Homotopic
        (genLoopPostcomp ((loopTailReplacement E).structureMap k) rfl q) p := by
  have hw := loopTailReplacement_structureMap_isWeakHomotopyEquivalence E k
  obtain ⟨a, ha⟩ := (hw.homotopy_bijective x n).surjective (Quotient.mk' p)
  induction a using Quotient.inductionOn with
  | h q => exact ⟨q, Quotient.exact ha⟩

/-- Whole homotopies after the unchanged structure adjoint reflect at every actual source point. -/
theorem original_arbitrary_point_source_homotopy_reflected (k n : ℕ)
    (x : (loopTailReplacement E).space k)
    (p q : GenLoop (Fin n) ((loopTailReplacement E).space k) x)
    (H : GenLoop.Homotopic
      (genLoopPostcomp ((loopTailReplacement E).structureMap k) rfl p)
      (genLoopPostcomp ((loopTailReplacement E).structureMap k) rfl q)) :
    GenLoop.Homotopic p q := by
  have hw := loopTailReplacement_structureMap_isWeakHomotopyEquivalence E k
  exact Quotient.exact ((hw.homotopy_bijective x n).injective (Quotient.sound H))

/-- Every original target loop has a genuine path from an image of the unchanged structure map. -/
theorem original_target_component_lifts (k : ℕ)
    (γ : Path ((loopTailReplacement E).point (k + 1)) ((loopTailReplacement E).point (k + 1))) :
    ∃ x : (loopTailReplacement E).space k,
      Nonempty (Path ((loopTailReplacement E).structureMap k x) γ) := by
  have hw := loopTailReplacement_structureMap_isWeakHomotopyEquivalence E k
  obtain ⟨x, hx⟩ := hw.component_surjective γ
  exact ⟨x, hx⟩

/-- The genuine Omega target retains the original initial inclusion on every signed stable class. -/
theorem original_initial_inclusion_stable_class_lifts (d : ℤ)
    (b : stableHomotopyGroup (loopTailReplacement E) d) :
    (loopTailReplacement E).IsOmega ∧
      ∃ a : stableHomotopyGroup E d,
        (stableHomotopyFunctor d).map (loopTailReplacementInclusion E) a = b := by
  refine ⟨loopTailReplacement_isOmega E,
    (loopTailReplacementStableHomotopyIso E d).inv b, ?_⟩
  rw [← loopTailReplacementStableHomotopyIso_hom E d]
  exact ConcreteCategory.congr_hom (loopTailReplacementStableHomotopyIso E d).inv_hom_id b

omit [∀ k, T1Space (E.space k)] in
/-- Original finite transitions preserve the actual loop coordinate at every positive stage. -/
theorem original_finite_transition_loop_parameter {i j : ℕ} (h : i ≤ j) (k : ℕ)
    (γ : Path ((loopTailIterate E i).point (k + 1)) ((loopTailIterate E i).point (k + 1)))
    (t : unitInterval) :
    Path.toContinuousMap ((Telescope.transition (loopTailIterate E) (loopTailTransition E)
      (i + 1) (j + 1) (Nat.succ_le_succ h)).map k γ :
        Path ((loopTailIterate E j).point (k + 1)) ((loopTailIterate E j).point (k + 1))) t =
      (Telescope.transition (loopTailIterate E) (loopTailTransition E) i j h).map
        (k + 1) (γ t) := loopTailFiniteTransition_apply E h k γ t

/-- The constant-prefix track commutes with the original map at every independent time. -/
theorem original_prefix_track_parameters {X Y : Type u} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) {x : X} {y : Y} (h : f x = y)
    (γ : Path x x) (s t : unitInterval) :
    basedLoopMap f h (loopLeftUnitPath γ s) t = loopLeftUnitPath (basedLoopMap f h γ) s t :=
  loopLeftUnitPath_naturality f h γ s t

end Quillen.Tests.LoopTailOmega
