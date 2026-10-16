/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Quillen.Waldhausen.SConstruction.Iterated.ChangedBoundaryPauseFaces

/-!
# Finite-simplex extension of the proved changed boundary

Only the actual finite real standard simplex is extended. The continuous boundary and all
its intersections were constructed in ChangedBoundaryPauseFaces. This does not invoke a
filler for an arbitrary target, or construct the later whole Bass boundary.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open Convexity Quillen.SimplexParameters Quillen.SimplexCubeExtension
open scoped Topology unitInterval
namespace Quillen.SimplexParameters.ChangedBoundaryPause
variable {k : ℕ} {a₀ b₀ a₁ b₁ : StdSimplex ℝ (Fin (k + 1))}
variable {p : Path a₀ b₀} {q : Path a₁ b₁}
variable {l : Path a₀ a₁} {m : Path b₀ b₁}
variable (J : p.Homotopy ((l.trans q).trans m.symm))

/-- Extend the already assembled scalar boundary by the finite-simplex extension theorem. -/
def cube : C(Cube, StdSimplex ℝ (Fin (k + 1))) :=
  cubeExtension k (boundaryMap J)

/-- The extension has exactly the constructed whole boundary, including the varying right edge. -/
theorem cube_boundary (x : boundary) : cube J x.val = boundaryMap J x :=
  cubeExtension_boundary k (boundaryMap J) x

/-- No face is inferred: every face is inherited from the proved boundary map. -/
theorem cube_face (a : Fin 3 × Bool) (x : face a) :
    cube J x.val.val = faceMap J a x :=
  (cube_boundary J x.val).trans (boundary_face J a x)

/-- Initial scalar square retains its exact original quotient-collapse parameter. -/
theorem cube_zero (r s : unitInterval) : cube J ![0, r, s] = collapsed J (r, s) := by
  let x : boundary := ⟨![0, r, s], ⟨0, Or.inl rfl⟩⟩
  exact cube_face J (0, false) ⟨x, rfl⟩

/-- Terminal scalar square is precisely the original pauseRight construction. -/
theorem cube_one (r s : unitInterval) :
    cube J ![1, r, s] = collapsed (pauseRightParameter J) (r, s) := by
  let x : boundary := ⟨![1, r, s], ⟨0, Or.inr rfl⟩⟩
  exact cube_face J (0, true) ⟨x, rfl⟩

/-- The source edge is fixed for every pause-comparison time. -/
theorem cube_source (a s : unitInterval) : cube J ![a, 0, s] = p s := by
  let x : boundary := ⟨![a, 0, s], ⟨1, Or.inl rfl⟩⟩
  exact cube_face J (1, false) ⟨x, rfl⟩

/-- The target edge is fixed without changing its original parametrization. -/
theorem cube_target (a s : unitInterval) : cube J ![a, 1, s] = q s := by
  let x : boundary := ⟨![a, 1, s], ⟨1, Or.inr rfl⟩⟩
  exact cube_face J (1, true) ⟨x, rfl⟩

/-- The left edge remains the original entire path. -/
theorem cube_left (a r : unitInterval) : cube J ![a, r, 0] = l r := by
  let x : boundary := ⟨![a, r, 0], ⟨2, Or.inl rfl⟩⟩
  exact cube_face J (2, false) ⟨x, rfl⟩

/-- The right edge genuinely changes from m to m.trans refl. -/
theorem cube_right (a r : unitInterval) :
    cube J ![a, r, 1] = rightEdge (m := m) (a, r) := by
  let x : boundary := ⟨![a, r, 1], ⟨2, Or.inr rfl⟩⟩
  exact cube_face J (2, true) ⟨x, rfl⟩

end Quillen.SimplexParameters.ChangedBoundaryPause
