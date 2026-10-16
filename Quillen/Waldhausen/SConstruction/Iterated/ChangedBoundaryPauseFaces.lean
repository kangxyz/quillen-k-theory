/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Quillen.Waldhausen.SConstruction.Iterated.ScalarChartPause
public import Quillen.Topology.Path.SimplexCollapsedEdges
public import Quillen.Topology.Realization.SimplexCubeFaces

/-!
# The actual six faces of a one-sided terminal pause

The right edge changes from m to m.trans refl by its specified transRefl homotopy.
The other three edges stay fixed. This draft only assembles the continuous boundary;
it does not define an interior cube or any higher Bass filler.
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

/-- The designated edge changes by the original terminal-pause homotopy. -/
def rightEdge : m.Homotopy (m.trans (Path.refl b₁)) :=
  (Path.Homotopy.transRefl m).symm

/-- Both scalar surfaces retain their original ThreeSideSquare collapse. -/
def faceMap (a : Fin 3 × Bool) : C(face a, StdSimplex ℝ (Fin (k + 1))) :=
  if a.1 = 0 then
    if a.2 then
      ⟨fun x ↦ collapsed (pauseRightParameter J) (x.val.val 1, x.val.val 2), by
        exact (collapsed (pauseRightParameter J)).continuous.comp
          (((continuous_apply (1 : Fin 3)).prodMk (continuous_apply 2)).comp
            (continuous_subtype_val.comp continuous_subtype_val))⟩
    else ⟨fun x ↦ collapsed J (x.val.val 1, x.val.val 2), by
      exact (collapsed J).continuous.comp
        (((continuous_apply (1 : Fin 3)).prodMk (continuous_apply 2)).comp
          (continuous_subtype_val.comp continuous_subtype_val))⟩
  else if a.1 = 1 then
    if a.2 then ⟨fun x ↦ q (x.val.val 2), by
      exact q.continuous.comp
        ((continuous_apply (2 : Fin 3)).comp
          (continuous_subtype_val.comp continuous_subtype_val))⟩
    else ⟨fun x ↦ p (x.val.val 2), by
      exact p.continuous.comp
        ((continuous_apply (2 : Fin 3)).comp
          (continuous_subtype_val.comp continuous_subtype_val))⟩
  else
    if a.2 then ⟨fun x ↦ rightEdge (m := m) (x.val.val 0, x.val.val 1), by
      exact (rightEdge (m := m)).continuous.comp
        (((continuous_apply (0 : Fin 3)).prodMk (continuous_apply 1)).comp
          (continuous_subtype_val.comp continuous_subtype_val))⟩
    else ⟨fun x ↦ l (x.val.val 1), by
      exact l.continuous.comp
        ((continuous_apply (1 : Fin 3)).comp
          (continuous_subtype_val.comp continuous_subtype_val))⟩

/-- The original starting square, at every point of its whole face. -/
theorem face_zero (x : face (0, false)) :
    faceMap J (0, false) x = collapsed J (x.val.val 1, x.val.val 2) := rfl

/-- The terminal square is precisely the existing pauseRight recipe. -/
theorem face_one (x : face (0, true)) :
    faceMap J (0, true) x =
      collapsed (pauseRightParameter J) (x.val.val 1, x.val.val 2) := rfl

/-- The whole designated side changes; no four-edge-relative assertion is made. -/
theorem face_right (x : face (2, true)) :
    faceMap J (2, true) x = rightEdge (m := m) (x.val.val 0, x.val.val 1) := rfl

/-- The twelve actual intersections, with the changed right edge at both square endpoints. -/
theorem faces_compatible : EdgeCompatible (fun a ↦ faceMap J a) := by
  intro i j hij a b x hi hj
  fin_cases i <;> fin_cases j <;> norm_num at hij
  all_goals
    cases a <;> cases b
    all_goals
      dsimp [faceMap]
      simp_all [face, endpoint, collapsed_zero_path, collapsed_top_path,
        collapsed_left_path, collapsed_right_path]

/-- A continuous whole boundary is produced from these proved face identities only. -/
def boundaryMap : C(boundary, StdSimplex ℝ (Fin (k + 1))) :=
  gluedBoundary k (faceMap J) (faces_compatible J)

/-- Every original face is retained pointwise by the assembled continuous boundary. -/
theorem boundary_face (a : Fin 3 × Bool) (x : face a) :
    boundaryMap J x.val = faceMap J a x :=
  gluedBoundary_face k (faceMap J) (faces_compatible J) a x

end Quillen.SimplexParameters.ChangedBoundaryPause
