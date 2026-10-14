/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeNative
public import Quillen.Topology.Realization.SimplexCubeFaces

/-! An exact cube on the six original scalar faces from their twelve proved whole edges. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open Convexity Quillen.SimplexCubeExtension
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassMWhole

/-- The original face parameters, read in their literal cube coordinate order. -/
def globalFaces (a : Fin 3 × Bool) : C(Cube, StdSimplex ℝ (Fin 140)) :=
  ![if a.2 then ⟨fun x ↦ h1Parameter.{u} (x 1, x 2), by fun_prop⟩
      else ⟨fun x ↦ h0Parameter (x 1, x 2), by fun_prop⟩,
    if a.2 then ⟨fun x ↦ mParameter.{u} (x 0, x 2), by fun_prop⟩
      else ⟨fun x ↦ bottomParameter.{u} (x 0, x 2), by fun_prop⟩,
    if a.2 then ⟨fun x ↦ minusParameter (x 0, x 1), by fun_prop⟩
      else ⟨fun x ↦ plusParameter (x 0, x 1), by fun_prop⟩] a.1

/-- Restrict each unchanged parameter family to its actual intrinsic whole cube face. -/
def faces (a : Fin 3 × Bool) : C(face a, StdSimplex ℝ (Fin 140)) :=
  ⟨fun x ↦ globalFaces.{u} a x.val.val, by fun_prop⟩

/-- All twelve nontrivial whole-edge intersections follow from the actual original scalar joins. -/
theorem face_compatible : EdgeCompatible (fun a ↦ faces.{u} a) := by
  intro i j hij b c x hi hj
  fin_cases i <;> fin_cases j <;> norm_num at hij
  all_goals cases b <;> cases c
  · change x.val 0 = 0 at hi
    change x.val 1 = 0 at hj
    change h0Parameter (x.val 1, x.val 2) =
      bottomParameter.{u} (x.val 0, x.val 2)
    rw [hi, hj]
    exact h0_bottom_scalar (x.val 2)
  · change x.val 0 = 0 at hi
    change x.val 1 = 1 at hj
    change h0Parameter (x.val 1, x.val 2) =
      mParameter.{u} (x.val 0, x.val 2)
    rw [hi, hj]
    exact (m_h0_scalar (x.val 2)).symm
  · change x.val 0 = 1 at hi
    change x.val 1 = 0 at hj
    change h1Parameter.{u} (x.val 1, x.val 2) =
      bottomParameter.{u} (x.val 0, x.val 2)
    rw [hi, hj]
    exact h1_bottom_scalar (x.val 2)
  · change x.val 0 = 1 at hi
    change x.val 1 = 1 at hj
    change h1Parameter.{u} (x.val 1, x.val 2) =
      mParameter.{u} (x.val 0, x.val 2)
    rw [hi, hj]
    exact (m_h1_scalar (x.val 2)).symm
  · change x.val 0 = 0 at hi
    change x.val 2 = 0 at hj
    change h0Parameter (x.val 1, x.val 2) =
      plusParameter (x.val 0, x.val 1)
    rw [hi, hj]
    exact h0_plus_scalar (x.val 1)
  · change x.val 0 = 0 at hi
    change x.val 2 = 1 at hj
    change h0Parameter (x.val 1, x.val 2) =
      minusParameter (x.val 0, x.val 1)
    rw [hi, hj]
    exact h0_minus_scalar (x.val 1)
  · change x.val 0 = 1 at hi
    change x.val 2 = 0 at hj
    change h1Parameter.{u} (x.val 1, x.val 2) =
      plusParameter (x.val 0, x.val 1)
    rw [hi, hj]
    exact h1_plus_scalar (x.val 1)
  · change x.val 0 = 1 at hi
    change x.val 2 = 1 at hj
    change h1Parameter.{u} (x.val 1, x.val 2) =
      minusParameter (x.val 0, x.val 1)
    rw [hi, hj]
    exact h1_minus_scalar (x.val 1)
  · change x.val 1 = 0 at hi
    change x.val 2 = 0 at hj
    change bottomParameter.{u} (x.val 0, x.val 2) =
      plusParameter (x.val 0, x.val 1)
    rw [hi, hj]
    exact (plus_bottom_scalar (x.val 0)).symm
  · change x.val 1 = 0 at hi
    change x.val 2 = 1 at hj
    change bottomParameter.{u} (x.val 0, x.val 2) =
      minusParameter (x.val 0, x.val 1)
    rw [hi, hj]
    exact (minus_bottom_scalar (x.val 0)).symm
  · change x.val 1 = 1 at hi
    change x.val 2 = 0 at hj
    change mParameter.{u} (x.val 0, x.val 2) =
      plusParameter (x.val 0, x.val 1)
    rw [hi, hj]
    exact m_plus_scalar (x.val 0)
  · change x.val 1 = 1 at hi
    change x.val 2 = 1 at hj
    change mParameter.{u} (x.val 0, x.val 2) =
      minusParameter (x.val 0, x.val 1)
    rw [hi, hj]
    exact m_minus_scalar (x.val 0)

/-- The accepted exact extension is now applied to the six actual fully compatible scalar faces. -/
def scalarCube : C(Cube, StdSimplex ℝ (Fin 140)) := fillFaces 139 faces.{u} face_compatible

/-- The extension keeps every point of each original whole face at its unchanged coordinates. -/
theorem cube_on_face (a : Fin 3 × Bool) (x : Cube) (h : x a.1 = endpoint a.2) :
    scalarCube.{u} x = globalFaces.{u} a x := by
  let xb : boundary := ⟨x, by
    cases hb : a.2 with
    | false => exact ⟨a.1, Or.inl (by
        simpa only [endpoint, hb, Bool.false_eq_true, ↓reduceIte] using h)⟩
    | true => exact ⟨a.1, Or.inr (by simpa only [endpoint, hb, ↓reduceIte] using h)⟩⟩
  exact fillFaces_face 139 faces.{u} face_compatible a ⟨xb, h⟩

theorem cube_zero (s t : unitInterval) : scalarCube.{u} ![0, s, t] = h0Parameter (s, t) :=
  cube_on_face (0, false) ![0, s, t] rfl

theorem cube_one (s t : unitInterval) : scalarCube.{u} ![1, s, t] = h1Parameter.{u} (s, t) :=
  cube_on_face (0, true) ![1, s, t] rfl

theorem cube_bottom (r t : unitInterval) : scalarCube.{u} ![r, 0, t] = bottomParameter.{u} (r, t) :=
  cube_on_face (1, false) ![r, 0, t] rfl

theorem cube_top (r t : unitInterval) : scalarCube.{u} ![r, 1, t] = mParameter.{u} (r, t) :=
  cube_on_face (1, true) ![r, 1, t] rfl

theorem cube_left (r s : unitInterval) : scalarCube.{u} ![r, s, 0] = plusParameter (r, s) :=
  cube_on_face (2, false) ![r, s, 0] rfl

theorem cube_right (r s : unitInterval) : scalarCube.{u} ![r, s, 1] = minusParameter (r, s) :=
  cube_on_face (2, true) ![r, s, 1] rfl

end Quillen.PerfectComplexes.BassMWhole
