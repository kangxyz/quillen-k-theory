/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.HomotopyFiber.GenLoopEvaluation

/-! # Original fiber-of-cubes evaluation and first-coordinate loop consumers -/
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
@[expose] public section
noncomputable section
open scoped Topology unitInterval
universe u v
namespace QuillenTest.GenLoopEvaluation
open Quillen Quillen.HomotopyFiber
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  (f : C(X, Y)) (y : Y) (x : X) (h : f x = y) (n : ℕ)
local notation "F" => genLoopPostcompContinuousMap (N := Fin (n + 1)) f h
local notation "B" => (GenLoop.const : GenLoop (Fin (n + 1)) Y y)

/-- Evaluation retains the original cube and the complete stored null path simultaneously. -/
theorem original_both_coordinates (w : HomotopyFiber F B)
    (z : Fin (n + 1) → unitInterval) (t : unitInterval) :
    (genLoopEvaluation f y x h n w z).val.1 = w.val.1 z ∧
      (genLoopEvaluation f y x h n w z).val.2 t = w.val.2 t z := ⟨rfl, rfl⟩

/-- The entire spatial boundary gives the fixed actual fiber point at every null time. -/
theorem original_whole_boundary (w : HomotopyFiber F B)
    (z : Fin (n + 1) → unitInterval) (hz : z ∈ Cube.boundary (Fin (n + 1))) :
    genLoopEvaluation f y x h n w z = basepoint f y x h :=
  genLoopEvaluation_boundary f y x h n w z hz

/-- Original projection recovers the complete source cube. -/
theorem original_projection (w : HomotopyFiber F B) :
    genLoopPostcomp (projection f y) (projection_basepoint f y x h)
      (genLoopEvaluation f y x h n w) = w.val.1 :=
  genLoopPostcomp_genLoopEvaluation f y x h n w

/-- The actual based fiber point evaluates to the actual constant cube. -/
theorem original_basepoint :
    genLoopEvaluation f y x h n
      (basepoint F B GenLoop.const (genLoopPostcomp_const f h)) = GenLoop.const :=
  genLoopEvaluation_basepoint f y x h n

/-- A full supplied relative nullhomotopy is retained by the existing lift construction. -/
theorem original_lift (p : GenLoop (Fin (n + 1)) X x)
    (H : (genLoopPostcomp f h p).val.HomotopyRel (B).val
      (Cube.boundary (Fin (n + 1)))) :
    genLoopEvaluation f y x h n
      ⟨(p, (genLoopPathOfHomotopyRel H).toContinuousMap),
        (genLoopPathOfHomotopyRel H).source, (genLoopPathOfHomotopyRel H).target⟩ =
      liftGenLoop f y x h p H :=
  genLoopEvaluation_liftGenLoop f y x h n p H

/-- The whole original loop-inclusion cube keeps every loop and spatial coordinate. -/
theorem original_loop_inclusion (L : Path B B) :
    genLoopEvaluation f y x h n
      (loopInclusion F B GenLoop.const (genLoopPostcomp_const f h) L) =
      genLoopPostcomp (loopInclusion f y x h) (loopInclusion_refl f y x h)
        (genLoopOfBasedPath L) :=
  genLoopEvaluation_loopInclusion f y x h n L

/-- The original first coordinate supplies loop time without a permutation. -/
theorem original_loop_curry (L : Path B B) :
    genLoopPostcomp (loopInclusion f y x h) (loopInclusion_refl f y x h)
      (loopCurry (loopUncurry (genLoopOfBasedPath L))) =
      genLoopEvaluation f y x h n
        (loopInclusion F B GenLoop.const (genLoopPostcomp_const f h) L) :=
  genLoopEvaluation_loopCurry f y x h n L

/-- The complete null-path evaluation remains jointly continuous in all three inputs. -/
theorem original_joint_continuity :
    Continuous (fun wzt : (HomotopyFiber F B × (Fin (n + 1) → unitInterval)) × unitInterval ↦
      (genLoopEvaluation f y x h n wzt.1.1 wzt.1.2).val.2 wzt.2) := by
  change Continuous
    (fun wzt : (HomotopyFiber F B × (Fin (n + 1) → unitInterval)) × unitInterval ↦
      wzt.1.1.val.2 wzt.2 wzt.1.2)
  fun_prop

/-- A one-dimensional original input still retains the exact loop-inclusion comparison. -/
theorem original_degree_zero
    (L : Path (GenLoop.const : GenLoop (Fin 1) Y y) GenLoop.const) :
    genLoopEvaluation f y x h 0
      (loopInclusion (genLoopPostcompContinuousMap (N := Fin 1) f h) GenLoop.const
        GenLoop.const (genLoopPostcomp_const f h) L) =
      genLoopPostcomp (loopInclusion f y x h) (loopInclusion_refl f y x h)
        (genLoopOfBasedPath L) :=
  genLoopEvaluation_loopInclusion f y x h 0 L

end QuillenTest.GenLoopEvaluation
