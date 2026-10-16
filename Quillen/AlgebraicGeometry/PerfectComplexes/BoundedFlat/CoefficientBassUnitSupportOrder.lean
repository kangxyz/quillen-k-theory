/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Order.Monotone.Defs

/-! A finite ordering certificate for the primitive supports of the original Bass unit cube.
The declarations prove only finite label equations and orders. They do not identify geometric
functors or common-reference nodes. Those independent mathematical equalities are required
before these labels can be used to transfer the actual six native faces. -/

@[expose] public section
set_option autoImplicit false

namespace Quillen.PerfectComplexes.CoefficientBassUnitSupportOrder

/-- Labels of the twenty-five polynomial-span top slots. -/
def topIndex : Fin 25 → Fin 48 :=
  ![8, 9, 14, 15, 16, 17, 18, 23, 24, 25, 27, 28,
    29, 30, 31, 32, 33, 34, 35, 36, 37, 42, 44, 45,
    47]

/-- Labels of the Bass projection by Laurent identity product slots. -/
def bottomIndex : Fin 15 → Fin 48 :=
  ![2, 3, 37, 4, 40, 42, 41, 43, 44, 5, 38, 45, 39, 46, 47]

/-- Labels of the positive Laurent unit square slots. -/
def plusSideIndex : Fin 8 → Fin 48 :=
  ![11, 12, 41, 43, 13, 14, 15, 44]

/-- Labels of the inverse Laurent unit square slots. -/
def minusSideIndex : Fin 8 → Fin 48 :=
  ![20, 21, 39, 46, 22, 23, 24, 47]

/-- Labels of the original thirty-one-slot projection-pasting diagram. -/
def h0Index : Fin 31 → Fin 48 :=
  ![0, 1, 2, 4, 6, 8, 9, 16, 10, 11, 12, 41,
    13, 14, 5, 7, 17, 18, 25, 19, 20, 21, 39, 22,
    23, 26, 27, 28, 29, 30, 31]

/-- The positive polynomial unit square inside the local top diagram. -/
def topPlusIndex : Fin 8 → Fin 25 :=
  ![0, 1, 2, 3, 4, 12, 17, 22]

/-- The inverse polynomial unit square inside the local top diagram. -/
def topMinusIndex : Fin 8 → Fin 25 :=
  ![5, 6, 7, 8, 9, 14, 19, 24]

/-- The original positive projection rectangle inside H0. -/
def h0PlusIndex : Fin 18 → Fin 31 :=
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 25, 26, 27, 28]

/-- The original inverse projection rectangle inside H0. -/
def h0MinusIndex : Fin 18 → Fin 31 :=
  ![0, 1, 2, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 29, 30]

/-- The six actual scalar triangles of an original unit square. -/
def unitTriangle : Fin 6 → Fin 3 → Fin 8 :=
  ![![0, 1, 2],
    ![2, 3, 7],
    ![0, 2, 7],
    ![0, 4, 5],
    ![5, 6, 7],
    ![0, 5, 7]]

/-- The eight identity-edge by projection-edge four-node supports in the top. -/
def topGridFace : Fin 8 → Fin 4 → Fin 25 :=
  ![![10, 11, 15, 16],
    ![11, 12, 16, 17],
    ![10, 13, 15, 18],
    ![13, 14, 18, 19],
    ![15, 16, 20, 21],
    ![16, 17, 21, 22],
    ![15, 18, 20, 23],
    ![18, 19, 23, 24]]

/-- The eight projection-edge by identity-edge four-node supports in the bottom. -/
def bottomGridFace : Fin 8 → Fin 4 → Fin 15 :=
  ![![0, 1, 3, 4],
    ![1, 2, 4, 5],
    ![3, 4, 6, 7],
    ![4, 5, 7, 8],
    ![0, 1, 9, 10],
    ![1, 2, 10, 11],
    ![9, 10, 12, 13],
    ![10, 11, 13, 14]]

/-- The six unchanged split-triple supports of the original H0 pasting. -/
def h0TripleFace : Fin 6 → Fin 8 → Fin 31 :=
  ![![0, 1, 2, 3, 8, 9, 10, 11],
    ![0, 4, 5, 6, 8, 9, 12, 13],
    ![0, 4, 5, 7, 25, 26, 27, 28],
    ![0, 1, 2, 14, 19, 20, 21, 22],
    ![0, 15, 16, 17, 19, 20, 23, 24],
    ![0, 15, 16, 18, 25, 26, 29, 30]]

/-- This primitive support remains in its exact original vertex order. -/
theorem top_plus_support :
    ∀ i : Fin 6, StrictMono (topIndex ∘ topPlusIndex ∘ unitTriangle i) := by decide

/-- This primitive support remains in its exact original vertex order. -/
theorem top_minus_support :
    ∀ i : Fin 6, StrictMono (topIndex ∘ topMinusIndex ∘ unitTriangle i) := by decide

/-- This primitive support remains in its exact original vertex order. -/
theorem plus_side_support : ∀ i : Fin 6, StrictMono (plusSideIndex ∘ unitTriangle i) := by decide

/-- This primitive support remains in its exact original vertex order. -/
theorem minus_side_support : ∀ i : Fin 6, StrictMono (minusSideIndex ∘ unitTriangle i) := by decide

/-- This primitive support remains in its exact original vertex order. -/
theorem top_grid_support : ∀ i : Fin 8, StrictMono (topIndex ∘ topGridFace i) := by decide

/-- This primitive support remains in its exact original vertex order. -/
theorem bottom_grid_support : ∀ i : Fin 8, StrictMono (bottomIndex ∘ bottomGridFace i) := by decide

/-- This primitive support remains in its exact original vertex order. -/
theorem h0_triple_support : ∀ i : Fin 6, StrictMono (h0Index ∘ h0TripleFace i) := by decide

/-- The positive top/side edge labels agree at both normalization steps. -/
theorem plus_top_labels : ∀ i : Fin 3,
    plusSideIndex (![5, 6, 7] i) = topIndex (![2, 3, 22] i) := by decide

/-- The inverse top/side edge has its separate actual labels. -/
theorem minus_top_labels : ∀ i : Fin 3,
    minusSideIndex (![5, 6, 7] i) = topIndex (![7, 8, 24] i) := by decide

/-- The positive bottom/side edge labels agree. -/
theorem plus_bottom_labels : ∀ i : Fin 3,
    plusSideIndex (![2, 3, 7] i) = bottomIndex (![6, 7, 8] i) := by decide

/-- The inverse bottom/side edge labels agree. -/
theorem minus_bottom_labels : ∀ i : Fin 3,
    minusSideIndex (![2, 3, 7] i) = bottomIndex (![12, 13, 14] i) := by decide

/-- The complete terminal projection path has five shared labels. -/
theorem terminal_projection_labels : ∀ i : Fin 5,
    bottomIndex (![2, 5, 8, 11, 14] i) = topIndex (![20, 21, 22, 23, 24] i) := by decide

/-- The five lower chart-path labels are shared with H0. -/
theorem h0_plus_side_labels : ∀ i : Fin 5,
    h0Index (h0PlusIndex (![9, 10, 11, 12, 13] i)) = plusSideIndex (![0, 1, 2, 4, 5] i) := by decide

/-- The five original polynomial square-path labels are shared with H0. -/
theorem h0_plus_top_labels : ∀ i : Fin 5,
    h0Index (h0PlusIndex (![5, 6, 13, 7, 17] i)) = topIndex (![0, 1, 2, 4, 12] i) := by decide

/-- The original source projection normalization path has matching labels. -/
theorem h0_plus_source_labels : ∀ i : Fin 3,
    h0Index (h0PlusIndex (![2, 3, 11] i)) = bottomIndex (![0, 3, 6] i) := by decide

/-- The original target projection normalization path has matching labels. -/
theorem h0_plus_target_labels : ∀ i : Fin 3,
    h0Index (h0PlusIndex (![15, 16, 17] i)) = topIndex (![10, 11, 12] i) := by decide

/-- The five lower chart-path labels are shared with H0. -/
theorem h0_minus_side_labels : ∀ i : Fin 5,
    h0Index (h0MinusIndex (![9, 10, 11, 12, 13] i)) =
      minusSideIndex (![0, 1, 2, 4, 5] i) := by decide

/-- The five original polynomial square-path labels are shared with H0. -/
theorem h0_minus_top_labels : ∀ i : Fin 5,
    h0Index (h0MinusIndex (![5, 6, 13, 7, 17] i)) = topIndex (![5, 6, 7, 9, 14] i) := by decide

/-- The original source projection normalization path has matching labels. -/
theorem h0_minus_source_labels : ∀ i : Fin 3,
    h0Index (h0MinusIndex (![2, 3, 11] i)) = bottomIndex (![0, 9, 12] i) := by decide

/-- The original target projection normalization path has matching labels. -/
theorem h0_minus_target_labels : ∀ i : Fin 3,
    h0Index (h0MinusIndex (![15, 16, 17] i)) = topIndex (![10, 13, 14] i) := by decide

/-- Both original projection rectangles retain their shared outer path. -/
theorem h0_outer_labels : ∀ i : Fin 5,
    h0Index (h0PlusIndex (![0, 1, 2, 14, 15] i)) =
      h0Index (h0MinusIndex (![0, 1, 2, 14, 15] i)) := by decide

end Quillen.PerfectComplexes.CoefficientBassUnitSupportOrder
