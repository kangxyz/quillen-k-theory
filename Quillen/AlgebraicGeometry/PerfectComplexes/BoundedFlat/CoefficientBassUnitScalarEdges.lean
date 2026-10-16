/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientPolynomialSpanUnitTop
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassUnitBottom
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.OriginalUnitSquareSupport
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassUnitSupportOrder
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassReindexedScalarEdges

/-! The six original unit-cube parameters and their twelve entire scalar edge equalities.
These equalities retain the original dyadic association, inverse-chart reversal and terminal
contractions, before any evaluation in a native common-reference family. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Convexity Quillen.SimplexParameters
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassUnitScalarEdges
open CoefficientBassUnitSupportOrder BassSupportOrder

def h0Parameter : C(unitInterval × unitInterval, StdSimplex ℝ (Fin 48)) :=
  ⟨fun z ↦ StdSimplex.map CoefficientBassUnitSupportOrder.h0Index
    (BassH0Diagram.parameter z), by fun_prop⟩

def topParameter : C(unitInterval × unitInterval, StdSimplex ℝ (Fin 48)) :=
  ⟨fun z ↦ StdSimplex.map topIndex (CoefficientPolynomialSpanUnitTop.topParameter.{u} z),
    by fun_prop⟩

def bottomParameter : C(unitInterval × unitInterval, StdSimplex ℝ (Fin 48)) :=
  ⟨fun z ↦ StdSimplex.map bottomIndex (CoefficientBassUnitBottom.parameter.{u} z),
    by fun_prop⟩

def plusParameter : C(unitInterval × unitInterval, StdSimplex ℝ (Fin 48)) :=
  ⟨fun z ↦ StdSimplex.map plusSideIndex (OriginalUnitSquareSimplex.squareParameter z),
    by fun_prop⟩

def minusParameter : C(unitInterval × unitInterval, StdSimplex ℝ (Fin 48)) :=
  ⟨fun z ↦ StdSimplex.map minusSideIndex (OriginalUnitSquareSimplex.squareParameter z),
    by fun_prop⟩

/-- The identity face is the unchanged terminal Bass projection path,
constant in comparison time. -/
def identityParameter : C(unitInterval × unitInterval, StdSimplex ℝ (Fin 48)) :=
  ⟨fun z ↦ StdSimplex.map topIndex (CoefficientPolynomialSpanUnitTop.middleEnd z.2),
    by fun_prop⟩

theorem h0_plus (s : unitInterval) : h0Parameter (s, 0) = plusParameter (0, s) := by
  change StdSimplex.map CoefficientBassUnitSupportOrder.h0Index _ =
    StdSimplex.map plusSideIndex _
  rw [BassH0Diagram.parameter_left, OriginalUnitSquareSimplex.square_zero]
  change StdSimplex.map CoefficientBassUnitSupportOrder.h0Index
      (((binaryPath (k := 30) 9 10 11).symm.trans (binaryPath 9 12 13)) s) =
    StdSimplex.map plusSideIndex
      (((binaryPath (k := 7) 0 1 2).symm.trans (binaryPath 0 4 5)) s)
  rw [map_two_binary, map_two_binary]
  rfl

theorem h0_minus (s : unitInterval) : h0Parameter (s, 1) = minusParameter (0, s) := by
  change StdSimplex.map CoefficientBassUnitSupportOrder.h0Index _ =
    StdSimplex.map minusSideIndex _
  rw [BassH0Diagram.parameter_right, OriginalUnitSquareSimplex.square_zero]
  change StdSimplex.map CoefficientBassUnitSupportOrder.h0Index
      (((binaryPath (k := 30) 20 21 22).symm.trans (binaryPath 20 23 24)) s) =
    StdSimplex.map minusSideIndex
      (((binaryPath (k := 7) 0 1 2).symm.trans (binaryPath 0 4 5)) s)
  rw [map_two_binary, map_two_binary]
  rfl

theorem h0_bottom (t : unitInterval) : h0Parameter (0, t) = bottomParameter.{u} (0, t) := by
  change StdSimplex.map CoefficientBassUnitSupportOrder.h0Index _ =
    StdSimplex.map bottomIndex _
  rw [BassH0Diagram.parameter_zero, CoefficientBassUnitBottom.parameter_zero]
  change StdSimplex.map CoefficientBassUnitSupportOrder.h0Index
      (((binaryPath (k := 30) 2 3 11).symm.trans (binaryPath 2 14 22)) t) =
    StdSimplex.map bottomIndex
      (StdSimplex.map (SimplexGrid.columnFace 4 2 0).toOrderHom
        (((binaryPath (k := 4) 0 1 2).symm.trans (binaryPath 0 3 4)) t))
  rw [← StdSimplex.map_comp, map_two_binary, map_two_binary]
  rfl

/-- The exact common lower top word, retaining its three original blocks and association. -/
def topWord : Path (StdSimplex.single 14 : StdSimplex ℝ (Fin 48))
    (StdSimplex.single 23) :=
  ((binaryPath 8 9 14).symm.trans (binaryPath 8 16 29)).trans
    (((binaryPath 27 28 29).symm.trans (binaryPath 27 30 31)).trans
      ((binaryPath 17 18 23).symm.trans (binaryPath 17 25 31)).symm)

theorem h0_top (t : unitInterval) : h0Parameter (1, t) = topParameter.{u} (0, t) := by
  change StdSimplex.map CoefficientBassUnitSupportOrder.h0Index _ = StdSimplex.map topIndex _
  rw [BassH0Diagram.parameter_one, CoefficientPolynomialSpanUnitTop.top_zero]
  trans topWord t
  · exact map_trans_values _ _ _ _ _
      (map_two_binary CoefficientBassUnitSupportOrder.h0Index 5 6 13 7 28)
      (map_trans_values _ _ _ _ _
        (map_two_binary CoefficientBassUnitSupportOrder.h0Index 26 27 28 29 30)
        (fun s ↦ map_two_binary CoefficientBassUnitSupportOrder.h0Index
          16 17 24 18 30 (unitInterval.symm s))) t
  · exact (map_trans_values _ _ _ _ _ (map_two_binary topIndex 0 1 2 4 12)
      (map_trans_values _ _ _ _ _ (map_two_binary topIndex 10 11 12 13 14)
        (fun s ↦ map_two_binary topIndex 5 6 7 9 14 (unitInterval.symm s))) t).symm

theorem identity_top (t : unitInterval) :
    identityParameter (1, t) = topParameter.{u} (1, t) := by
  change StdSimplex.map topIndex _ = StdSimplex.map topIndex _
  rw [CoefficientPolynomialSpanUnitTop.top_one]

theorem identity_bottom (t : unitInterval) :
    identityParameter (0, t) = bottomParameter.{u} (1, t) := by
  change StdSimplex.map topIndex _ = StdSimplex.map bottomIndex _
  rw [CoefficientBassUnitBottom.parameter_one]
  change StdSimplex.map topIndex
      (((binaryPath (k := 24) 20 21 22).symm.trans (binaryPath 20 23 24)) t) =
    StdSimplex.map bottomIndex
      (StdSimplex.map (SimplexGrid.columnFace 4 2 2).toOrderHom
        (((binaryPath (k := 4) 0 1 2).symm.trans (binaryPath 0 3 4)) t))
  rw [← StdSimplex.map_comp, map_two_binary, map_two_binary]
  rfl

theorem identity_plus (s : unitInterval) : identityParameter (s, 0) = plusParameter (1, s) := by
  change StdSimplex.map topIndex _ = StdSimplex.map plusSideIndex _
  rw [CoefficientPolynomialSpanUnitTop.middleEnd.source,
    OriginalUnitSquareSupport.square_top_path, StdSimplex.map_single, StdSimplex.map_single]
  rfl

theorem identity_minus (s : unitInterval) :
    identityParameter (s, 1) = minusParameter (1, s) := by
  change StdSimplex.map topIndex _ = StdSimplex.map minusSideIndex _
  rw [CoefficientPolynomialSpanUnitTop.middleEnd.target,
    OriginalUnitSquareSupport.square_top_path, StdSimplex.map_single, StdSimplex.map_single]
  rfl

theorem top_plus (r : unitInterval) : topParameter.{u} (r, 0) = plusParameter (r, 1) := by
  change StdSimplex.map topIndex _ = StdSimplex.map plusSideIndex _
  rw [CoefficientPolynomialSpanUnitTop.top_left, OriginalUnitSquareSupport.square_right_path]
  change StdSimplex.map topIndex (binaryPath (k := 24) 2 3 22 r) =
    StdSimplex.map plusSideIndex (binaryPath (k := 7) 5 6 7 r)
  rw [map_any_binary, map_any_binary]
  rfl

theorem top_minus (r : unitInterval) : topParameter.{u} (r, 1) = minusParameter (r, 1) := by
  change StdSimplex.map topIndex _ = StdSimplex.map minusSideIndex _
  rw [CoefficientPolynomialSpanUnitTop.top_right, OriginalUnitSquareSupport.square_right_path]
  change StdSimplex.map topIndex (binaryPath (k := 24) 7 8 24 r) =
    StdSimplex.map minusSideIndex (binaryPath (k := 7) 5 6 7 r)
  rw [map_any_binary, map_any_binary]
  rfl

theorem bottom_plus (r : unitInterval) :
    bottomParameter.{u} (r, 0) = plusParameter (r, 0) := by
  change StdSimplex.map bottomIndex _ = StdSimplex.map plusSideIndex _
  rw [CoefficientBassUnitBottom.parameter_left, OriginalUnitSquareSupport.square_left_path]
  change StdSimplex.map bottomIndex (binaryPath (k := 14) 6 7 8 r) =
    StdSimplex.map plusSideIndex (binaryPath (k := 7) 2 3 7 r)
  rw [map_any_binary, map_any_binary]
  rfl

theorem bottom_minus (r : unitInterval) :
    bottomParameter.{u} (r, 1) = minusParameter (r, 0) := by
  change StdSimplex.map bottomIndex _ = StdSimplex.map minusSideIndex _
  rw [CoefficientBassUnitBottom.parameter_right, OriginalUnitSquareSupport.square_left_path]
  change StdSimplex.map bottomIndex (binaryPath (k := 14) 12 13 14 r) =
    StdSimplex.map minusSideIndex (binaryPath (k := 7) 2 3 7 r)
  rw [map_any_binary, map_any_binary]
  rfl

end Quillen.PerfectComplexes.CoefficientBassUnitScalarEdges
