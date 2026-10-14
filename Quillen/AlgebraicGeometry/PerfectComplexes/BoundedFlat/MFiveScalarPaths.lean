/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.H1EightEdges

/-! The five original reassociation paths inside the fixed actual H1 reference simplex. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Convexity Quillen.SimplexParameters Quillen.NativePathCells
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassMReassociation

/-- The actual first positive path, with all five fixed common-node labels retained. -/
def Ppath := (binaryPath (k := 130) 52 78 80).symm.trans (binaryPath 52 85 122)

/-- The actual second positive path from the middle H0 target. -/
def Qpath := (binaryPath (k := 130) 35 36 122).symm.trans (binaryPath 35 37 45)

/-- The original central Bass projection path after both coefficient maps. -/
def Tpath := (binaryPath (k := 130) 43 44 45).symm.trans (binaryPath 43 46 47)

/-- The separate inverse middle path retains its complete original reversal. -/
def Upath := ((binaryPath (k := 130) 39 40 130).symm.trans (binaryPath 39 41 47)).symm

/-- The final inverse path retains both normalization pieces and its original reversed time. -/
def Vpath := ((binaryPath (k := 130) 90 107 109).symm.trans (binaryPath 90 128 130)).symm

/-- The whole first path is exactly the fixed positive H1 product endpoint family. -/
theorem P_value (t : unitInterval) : Ppath t = BassH1Order.plusProductParameter.{u} (1, t) := by
  change Ppath t = StdSimplex.map BassH1Order.plusProductIndex
    (Quillen.SimplexGrid.parameter.{u + 1} 4 4
      (NativeSquareFiveSimplex.parameter t, NativeSquareFiveSimplex.parameter 1))
  rw [Path.target]
  have hc := congrArg (StdSimplex.map BassH1Order.plusProductIndex)
    (Quillen.SimplexGrid.parameter_column.{u + 1} 4 4 4 (NativeSquareFiveSimplex.parameter t))
  refine Eq.trans ?_ hc.symm
  exact (BassSupportOrder.map_two_binary
    (BassH1Order.plusProductIndex ∘ (Quillen.SimplexGrid.columnFace 4 4 4).toOrderHom)
    0 1 2 3 4 t).symm.trans
    (StdSimplex.map_comp (NativeSquareFiveSimplex.parameter t)
      (Quillen.SimplexGrid.columnFace 4 4 4).toOrderHom BassH1Order.plusProductIndex)

/-- The whole second path uses the original first half of the middle target cylinder. -/
theorem Q_value (t : unitInterval) : Qpath t = BassH1Order.middleParameter (1, lower t) := by
  have hm := (BassSupportOrder.map_two_binary
    (fun i ↦ BassH1Order.middleIndex
      (BassH0Diagram.plusFace.toOrderHom (BassH1Join.polynomialWordIndex i)))
    0 1 2 3 4 t).symm.trans
    (StdSimplex.map_comp (NativeSquareFiveSimplex.parameter t)
      (fun i ↦ BassH0Diagram.plusFace.toOrderHom (BassH1Join.polynomialWordIndex i))
      BassH1Order.middleIndex)
  exact hm.trans (congrArg (StdSimplex.map BassH1Order.middleIndex)
    (BassH1Join.first_plus_parameter t))

/-- The complete central path retains the original middle-quarter cylinder parameter. -/
theorem T_value (t : unitInterval) :
    Tpath t = BassH1Order.middleParameter (1, upper (lower t)) := by
  have hm := (BassSupportOrder.map_two_binary
    (BassH1Order.middleIndex ∘ BassH1Join.firstMiddleFace.toOrderHom) 0 1 2 3 4 t).symm.trans
    (StdSimplex.map_comp (NativeSquareFiveSimplex.parameter t)
      BassH1Join.firstMiddleFace.toOrderHom BassH1Order.middleIndex)
  exact hm.trans (congrArg (StdSimplex.map BassH1Order.middleIndex)
    (BassH1Join.first_middle_parameter t))

/-- The complete inverse middle path retains the original final quarter and time reversal. -/
theorem U_value (t : unitInterval) :
    Upath t = BassH1Order.middleParameter (1, upper (upper t)) := by
  have hm := (BassSupportOrder.map_two_binary
    (fun i ↦ BassH1Order.middleIndex
      (BassH0Diagram.minusFace.toOrderHom (BassH1Join.polynomialWordIndex i)))
    0 1 2 3 4 (unitInterval.symm t)).symm.trans
    (StdSimplex.map_comp (NativeSquareFiveSimplex.parameter (unitInterval.symm t))
      (fun i ↦ BassH0Diagram.minusFace.toOrderHom (BassH1Join.polynomialWordIndex i))
      BassH1Order.middleIndex)
  exact hm.trans (congrArg (StdSimplex.map BassH1Order.middleIndex)
    (BassH1Join.first_minus_parameter t))

/-- The entire final path is the fixed inverse H1 product endpoint family. -/
theorem V_value (t : unitInterval) : Vpath t = BassH1Order.minusProductParameter.{u} (1, t) := by
  change Vpath t = StdSimplex.map BassH1Order.minusProductIndex
    (Quillen.SimplexGrid.parameter.{u + 1} 4 4
      (NativeSquareFiveSimplex.parameter (unitInterval.symm t),
        NativeSquareFiveSimplex.parameter 1))
  rw [Path.target]
  have hc := congrArg (StdSimplex.map BassH1Order.minusProductIndex)
    (Quillen.SimplexGrid.parameter_column.{u + 1} 4 4 4
      (NativeSquareFiveSimplex.parameter (unitInterval.symm t)))
  refine Eq.trans ?_ hc.symm
  exact (BassSupportOrder.map_two_binary
    (BassH1Order.minusProductIndex ∘ (Quillen.SimplexGrid.columnFace 4 4 4).toOrderHom)
    0 1 2 3 4 (unitInterval.symm t)).symm.trans
    (StdSimplex.map_comp (NativeSquareFiveSimplex.parameter (unitInterval.symm t))
      (Quillen.SimplexGrid.columnFace 4 4 4).toOrderHom BassH1Order.minusProductIndex)

/-- All middle target parameters retain exactly the original three-piece path word. -/
theorem middle_word (t : unitInterval) :
    BassH1Order.middleParameter (1, t) = (Qpath.trans (Tpath.trans Upath)) t := by
  rcases three_cover t with ⟨r, rfl⟩ | ⟨r, rfl⟩ | ⟨r, rfl⟩
  · rw [← Q_value, path_lower]
  · rw [← T_value, path_upper, path_lower]
  · rw [← U_value, path_upper, path_upper]

/-- The complete original H1 target is the actual five-piece word, with its native associations. -/
theorem h1_target_word (t : unitInterval) :
    BassH1Order.h1Parameter.{u} (1, t) =
      (Ppath.trans ((Qpath.trans (Tpath.trans Upath)).trans Vpath)) t := by
  rw [BassH1Order.h1_one]
  rcases three_cover t with ⟨r, rfl⟩ | ⟨r, rfl⟩ | ⟨r, rfl⟩
  · rw [BassH1Order.second_lower, ← P_value, path_lower]
  · rw [BassH1Order.second_middle, middle_word, path_upper, path_lower]
  · rw [BassH1Order.second_upper, ← V_value, path_upper, path_upper]

/-- The original three-associator word, constructed on these unchanged five complete paths. -/
def reassociation : (Ppath.trans ((Qpath.trans (Tpath.trans Upath)).trans Vpath)).Homotopy
    ((Ppath.trans Qpath).trans (Tpath.trans (Upath.trans Vpath))) :=
  ((Path.Homotopy.refl Ppath).hcomp
    (Path.Homotopy.transAssoc Qpath (Tpath.trans Upath) Vpath)).trans
    (((Path.Homotopy.refl Ppath).hcomp
      ((Path.Homotopy.refl Qpath).hcomp (Path.Homotopy.transAssoc Tpath Upath Vpath))).trans
      (Path.Homotopy.transAssoc Ppath Qpath (Tpath.trans (Upath.trans Vpath))).symm)

end Quillen.PerfectComplexes.BassMReassociation
