/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassUnitBottom
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassUnitSupportOrder
public import Quillen.Topology.Realization.SimplexGridProductFaces
public import Quillen.Topology.Path.ParameterRangeClosure

/-! The actual bottom product is covered by eight original four-node grid faces.
Coverage follows from the genuine realization-product map on each pair of edges. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory Convexity Quillen.SimplexParameters Quillen.ParameterSupport
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassUnitBottomSupport
open CoefficientBassUnitSupportOrder Quillen.SimplexGrid

def projectionStart : Fin 4 → Fin 5 := ![0, 1, 0, 3]
def projectionEnd : Fin 4 → Fin 5 := ![1, 2, 3, 4]
def identityStart : Fin 2 → Fin 3 := ![0, 1]
def identityEnd : Fin 2 → Fin 3 := ![1, 2]

def projectionFace (i : Fin 4) : ⦋1⦌ ⟶ ⦋4⦌ :=
  SimplexCategory.Hom.mk ⟨![projectionStart i, projectionEnd i],
    (by decide : ∀ j : Fin 4, Monotone
      (![projectionStart j, projectionEnd j] : Fin 2 → Fin 5)) i⟩

def identityFace (i : Fin 2) : ⦋1⦌ ⟶ ⦋2⦌ :=
  SimplexCategory.Hom.mk ⟨![identityStart i, identityEnd i],
    (by decide : ∀ j : Fin 2, Monotone
      (![identityStart j, identityEnd j] : Fin 2 → Fin 3)) i⟩

def face (i : Fin 8) : ⦋3⦌ ⟶ ⦋14⦌ :=
  SimplexCategory.Hom.mk ⟨bottomGridFace i,
    (by decide : ∀ j : Fin 8, Monotone (bottomGridFace j)) i⟩

def pairIndex (i : Fin 4) (j : Fin 2) : Fin 8 := ⟨2 * i.val + j.val, by omega⟩

/-- Each finite face preserves the exact row-major index of both original edge coordinates. -/
theorem face_pair (i : Fin 4) (j : Fin 2) (k l : Fin 2) :
    (face (pairIndex i j)).toOrderHom (index 1 1 (k, l)) =
      index 4 2 ((projectionFace i).toOrderHom k, (identityFace j).toOrderHom l) := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;> rfl

/-- The genuine product parameter on each original pair of edges has its exact small face. -/
theorem parameter_pair (i : Fin 4) (j : Fin 2) (z w : StdSimplex ℝ (Fin 2)) :
    SimplexGrid.parameter.{u} 4 2
      (StdSimplex.map (projectionFace i).toOrderHom z,
        StdSimplex.map (identityFace j).toOrderHom w) =
      StdSimplex.map (face (pairIndex i j)).toOrderHom
        (SimplexGrid.parameter.{u} 1 1 (z, w)) :=
  parameter_productMap (projectionFace i) (identityFace j) (face (pairIndex i j))
    (face_pair i j) z w

def projectionSupport : Set (StdSimplex ℝ (Fin 5)) :=
  {z | ∃ (i : Fin 4) (w : StdSimplex ℝ (Fin 2)),
    StdSimplex.map (projectionFace i).toOrderHom w = z}

def identitySupport : Set (StdSimplex ℝ (Fin 3)) :=
  {z | ∃ (i : Fin 2) (w : StdSimplex ℝ (Fin 2)),
    StdSimplex.map (identityFace i).toOrderHom w = z}

theorem projection_edge_in (i : Fin 4) :
    PathIn projectionSupport (edge (projectionStart i) (projectionEnd i)) := by
  intro t
  exact ⟨i, edge (k := 1) 0 1 t,
    StdSimplex.map_duple (unitInterval.nonneg (unitInterval.symm t))
      (unitInterval.nonneg t) (by simp) _ _ _⟩

theorem identity_edge_in (i : Fin 2) :
    PathIn identitySupport (edge (identityStart i) (identityEnd i)) := by
  intro t
  exact ⟨i, edge (k := 1) 0 1 t,
    StdSimplex.map_duple (unitInterval.nonneg (unitInterval.symm t))
      (unitInterval.nonneg t) (by simp) _ _ _⟩

theorem projection_path_in : PathIn projectionSupport BassProjectionPath.parameter :=
  path_trans (path_symm (path_trans (projection_edge_in 0) (projection_edge_in 1)))
    (path_trans (projection_edge_in 2) (projection_edge_in 3))

theorem identity_path_in : PathIn identitySupport (binaryPath (k := 2) 0 1 2) :=
  path_trans (identity_edge_in 0) (identity_edge_in 1)

/-- Every bottom value is on one of the eight actual grid supports in the fixed order. -/
theorem bottom_support (z : unitInterval × unitInterval) :
    ∃ (i : Fin 8) (w : StdSimplex ℝ (Fin 4)),
      StdSimplex.map (face i).toOrderHom w = CoefficientBassUnitBottom.parameter.{u} z := by
  obtain ⟨i, v, hv⟩ := projection_path_in z.2
  obtain ⟨j, w, hw⟩ := identity_path_in z.1
  refine ⟨pairIndex i j, SimplexGrid.parameter.{u + 1} 1 1 (v, w), ?_⟩
  rw [← parameter_pair, hv, hw]
  rfl

end Quillen.PerfectComplexes.CoefficientBassUnitBottomSupport
