/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Quillen.Topology.Cube.StickBreakingFaces
import Quillen.Topology.HomotopyGroups.SphericalSimplexQuotient

/-! Regression checks for the explicit quotient, including all tetrahedral faces. -/

open Convexity Quillen
open scoped Topology unitInterval
noncomputable section
universe u

example (t : Fin 0 → I) : Cube.stickBreaking 0 t = StdSimplex.single 0 :=
  by
    apply StdSimplex.ext
    ext i
    have hi : i = 0 := Fin.ext (by omega)
    subst i
    simp

example (t u v : I) :
    (Cube.stickBreaking 3 ![t, u, v]).weights 0 = (t : ℝ) ∧
    (Cube.stickBreaking 3 ![t, u, v]).weights 1 = (1 - (t : ℝ)) * u ∧
    (Cube.stickBreaking 3 ![t, u, v]).weights 2 = (1 - (t : ℝ)) * ((1 - (u : ℝ)) * v) ∧
    (Cube.stickBreaking 3 ![t, u, v]).weights 3 =
      (1 - (t : ℝ)) * ((1 - (u : ℝ)) * (1 - (v : ℝ))) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  change (1 - (t : ℝ)) * ((1 - (u : ℝ)) * ((1 - (v : ℝ)) * 1)) = _
  rw [mul_one]

example (t : Fin 2 → I) :
    Cube.stickBreaking 3 ((0 : Fin 3).insertNth 0 t) =
      (Cube.stickBreaking 2 t).map (0 : Fin 4).succAbove ∧
    Cube.stickBreaking 3 ((1 : Fin 3).insertNth 0 t) =
      (Cube.stickBreaking 2 t).map (1 : Fin 4).succAbove ∧
    Cube.stickBreaking 3 ((2 : Fin 3).insertNth 0 t) =
      (Cube.stickBreaking 2 t).map (2 : Fin 4).succAbove ∧
    Cube.stickBreaking 3 (Fin.snoc t 1) =
      (Cube.stickBreaking 2 t).map (3 : Fin 4).succAbove :=
  ⟨Cube.stickBreaking_lower_face 2 0 t, Cube.stickBreaking_lower_face 2 1 t,
    Cube.stickBreaking_lower_face 2 2 t, Cube.stickBreaking_upper_last 2 t⟩

example (t : Fin 2 → I) :
    (∃ i k : Fin 4, i ≠ k ∧
      (Cube.stickBreaking 3 ((0 : Fin 3).insertNth 1 t)).weights i = 0 ∧
      (Cube.stickBreaking 3 ((0 : Fin 3).insertNth 1 t)).weights k = 0) ∧
    (∃ i k : Fin 4, i ≠ k ∧
      (Cube.stickBreaking 3 ((1 : Fin 3).insertNth 1 t)).weights i = 0 ∧
      (Cube.stickBreaking 3 ((1 : Fin 3).insertNth 1 t)).weights k = 0) :=
  ⟨Cube.stickBreaking_upper_two_zero 0 (by decide) t,
    Cube.stickBreaking_upper_two_zero 1 (by decide) t⟩

example : ¬ Function.Injective (Cube.stickBreaking 2) := Cube.stickBreaking_two_not_injective

example {Z : Type u} [TopologicalSpace Z] {z : Z} (p : GenLoop (Fin 2) Z z) :
    (SphericalSimplex.ofGenLoopStick p).homotopyClassStick = Quotient.mk' p := by
  simp only [SphericalSimplex.homotopyClassStick,
    SphericalSimplex.toGenLoopStick_ofGenLoopStick]
  rfl

example {Z : Type u} [TopologicalSpace Z] {z : Z} (f : SphericalSimplex Z z 2) :
    f.homotopyClassStick = 1 ↔ f.homotopyClass = 1 :=
  f.homotopyClassStick_eq_one_iff_chosen

example {Z : Type u} [TopologicalSpace Z] {z : Z} (f g : SphericalSimplex Z z 2)
    (H : f.toGenLoopStick.val.HomotopyRel g.toGenLoopStick.val (_root_.Cube.boundary (Fin 2))) :
    f.val.HomotopicRel g.val (simplexBoundary 2) :=
  ⟨SphericalSimplex.homotopyFromGenLoopStick H⟩

example {Z : Type u} [TopologicalSpace Z] {z : Z} (f g : SphericalSimplex Z z 2)
    (H : f.toGenLoopStick.val.HomotopyRel g.toGenLoopStick.val (_root_.Cube.boundary (Fin 2)))
    (s : I) (t : Fin 2 → I) :
    SphericalSimplex.homotopyFromGenLoopStick H (s, Cube.stickBreaking 2 t) = H (s, t) :=
  SphericalSimplex.homotopyFromGenLoopStick_apply_stick H s t
