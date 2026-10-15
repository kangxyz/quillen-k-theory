/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.H1OuterNodeJoins
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.H1ProductSupport

/-! Finite scalar indexing for the actual 57 supported H0, H1, chart and bottom faces. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory Convexity
open scoped Simplicial Topology unitInterval
namespace Quillen.PerfectComplexes.BassH1Order

/-- Reindexes the old 63-node family in the common 131-slot family. -/
def oldIndex : Fin 63 → Fin 131 := ![
  0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14,
  15, 16, 17, 20, 21, 22, 23, 24, 25, 26, 27, 57, 58, 59, 60,
  75, 79, 80, 76, 77, 61, 28, 29, 62, 63, 64, 65, 66, 67, 68,
  69, 70, 71, 95, 96, 97, 98, 104, 108, 109, 105, 106, 99, 72, 73,
  100, 101, 102]

/-- Reindexes the first 31-node H1 component in the common 131-slot family. -/
def firstIndex : Fin 31 → Fin 131 := ![
  18, 19, 20, 29, 30, 50, 55, 83, 56, 57, 59, 64, 58, 77, 73,
  31, 88, 93, 112, 94, 95, 97, 102, 96, 106, 113, 114, 115, 120, 116,
  127]

/-- Reindexes the middle 31-node H1 component in the common 131-slot family. -/
def middleIndex : Fin 31 → Fin 131 := ![
  32, 33, 114, 115, 34, 35, 36, 37, 117, 118, 119, 120, 121, 122, 116,
  38, 39, 40, 41, 123, 125, 126, 127, 129, 130, 42, 43, 44, 45, 46,
  47]

/-- Reindexes the 25 positive product-grid nodes in the common 131-slot family. -/
def plusProductIndex : Fin 25 → Fin 131 := ![
  48, 49, 50, 51, 52, 53, 54, 55, 74, 78, 75, 76, 77, 79, 80,
  81, 82, 83, 84, 85, 118, 119, 120, 121, 122]

/-- Reindexes the 25 inverse product-grid nodes in the common 131-slot family. -/
def minusProductIndex : Fin 25 → Fin 131 := ![
  86, 87, 88, 89, 90, 91, 92, 93, 103, 107, 104, 105, 106, 108, 109,
  110, 111, 112, 124, 128, 125, 126, 127, 129, 130]

theorem oldPlus_monotone (i : Fin 3) :
    Monotone (oldIndex ∘ (BassSupportOrder.oldPlusFace i).toOrderHom) := by
  fin_cases i <;> decide

theorem oldMinus_monotone (i : Fin 3) :
    Monotone (oldIndex ∘ (BassSupportOrder.oldMinusFace i).toOrderHom) := by
  fin_cases i <;> decide

theorem oldH0Plus_monotone (i : Fin 3) :
    Monotone (oldIndex ∘ (BassSupportOrder.h0PlusFace i).toOrderHom) := by
  fin_cases i <;> decide

theorem oldH0Minus_monotone (i : Fin 3) :
    Monotone (oldIndex ∘ (BassSupportOrder.h0MinusFace i).toOrderHom) := by
  fin_cases i <;> decide

theorem oldBottom_monotone : Monotone (oldIndex ∘ BassSupportOrder.bottomFace.toOrderHom) := by
  decide

theorem firstPlus_monotone (i : Fin 3) :
    Monotone (firstIndex ∘
      (BassPrimitiveSupport.rectangleFace i ≫ BassH0Diagram.plusFace).toOrderHom) := by
  fin_cases i <;> decide

theorem firstMinus_monotone (i : Fin 3) :
    Monotone (firstIndex ∘
      (BassPrimitiveSupport.rectangleFace i ≫ BassH0Diagram.minusFace).toOrderHom) := by
  fin_cases i <;> decide

theorem middlePlus_monotone (i : Fin 3) :
    Monotone (middleIndex ∘
      (BassPrimitiveSupport.rectangleFace i ≫ BassH0Diagram.plusFace).toOrderHom) := by
  fin_cases i <;> decide

theorem middleMinus_monotone (i : Fin 3) :
    Monotone (middleIndex ∘
      (BassPrimitiveSupport.rectangleFace i ≫ BassH0Diagram.minusFace).toOrderHom) := by
  fin_cases i <;> decide

theorem plusProduct_monotone (i j : Fin 4) :
    Monotone (plusProductIndex ∘ (BassH1Support.edgePairFace i j).toOrderHom) := by
  fin_cases i <;> fin_cases j <;> decide

theorem minusProduct_monotone (i j : Fin 4) :
    Monotone (minusProductIndex ∘ (BassH1Support.edgePairFace i j).toOrderHom) := by
  fin_cases i <;> fin_cases j <;> decide

theorem pair0_indices (i : Fin 5) :
    firstIndex (![26, 27, 28, 29, 30] i) =
      middleIndex (![2, 3, 11, 14, 22] i) := by
  fin_cases i <;> rfl

theorem pair1_indices (i : Fin 5) :
    firstIndex (![5, 6, 13, 7, 28] i) =
      plusProductIndex (![2, 7, 12, 17, 22] i) := by
  fin_cases i <;> rfl

theorem pair2_indices (i : Fin 5) :
    firstIndex (![16, 17, 24, 18, 30] i) =
      minusProductIndex (![2, 7, 12, 17, 22] i) := by
  fin_cases i <;> rfl

theorem pair3_indices (i : Fin 5) :
    middleIndex (![9, 10, 11, 12, 13] i) =
      plusProductIndex (![20, 21, 22, 23, 24] i) := by
  fin_cases i <;> rfl

theorem pair4_indices (i : Fin 5) :
    middleIndex (![20, 21, 22, 23, 24] i) =
      minusProductIndex (![20, 21, 22, 23, 24] i) := by
  fin_cases i <;> rfl

theorem pair5_indices (i : Fin 5) :
    firstIndex (![2, 3, 11, 14, 22] i) =
      oldIndex (![18, 37, 40, 59, 62] i) := by
  fin_cases i <;> rfl

theorem pair6_indices (i : Fin 5) :
    firstIndex (![9, 10, 11, 12, 13] i) =
      oldIndex (![26, 28, 40, 27, 34] i) := by
  fin_cases i <;> rfl

theorem pair7_indices (i : Fin 5) :
    firstIndex (![20, 21, 22, 23, 24] i) =
      oldIndex (![48, 50, 62, 49, 56] i) := by
  fin_cases i <;> rfl

theorem pair8_indices (i : Fin 5) :
    plusProductIndex (![10, 11, 12, 13, 14] i) =
      oldIndex (![30, 33, 34, 31, 32] i) := by
  fin_cases i <;> rfl

theorem pair9_indices (i : Fin 5) :
    minusProductIndex (![10, 11, 12, 13, 14] i) =
      oldIndex (![52, 55, 56, 53, 54] i) := by
  fin_cases i <;> rfl

end Quillen.PerfectComplexes.BassH1Order
