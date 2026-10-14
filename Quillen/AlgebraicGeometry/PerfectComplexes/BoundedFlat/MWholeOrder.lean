/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.H1SupportOrder
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MSourceBoundaryNodes
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MAllBoundaryNodes
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MGridProductFaces

/-! Fixed finite quotient order for the actual 176 H1/M input slots. -/
@[expose] public section
set_option autoImplicit false
open CategoryTheory
open Quillen.PerfectComplexes
namespace Quillen.PerfectComplexes.BassMWholeOrder

def oldChunk0 : Fin 10 → Fin 140 :=
![
  0, 1, 2, 3, 60, 4, 5, 6, 102, 7
]
def oldChunk1 : Fin 10 → Fin 140 :=
![
  8, 9, 10, 11, 12, 13, 14, 15, 16, 17
]
def oldChunk2 : Fin 10 → Fin 140 :=
![
  18, 19, 61, 62, 63, 64, 65, 66, 20, 21
]
def oldChunk3 : Fin 10 → Fin 140 :=
![
  22, 23, 24, 25, 26, 87, 88, 89, 27, 125
]
def oldChunk4 : Fin 10 → Fin 140 :=
![
  126, 127, 128, 129, 130, 131, 132, 133, 28, 29
]
def oldChunk5 : Fin 10 → Fin 140 :=
![
  30, 31, 57, 32, 33, 34, 35, 67, 68, 69
]
def oldChunk6 : Fin 10 → Fin 140 :=
![
  70, 71, 72, 73, 74, 75, 103, 104, 105, 106
]
def oldChunk7 : Fin 10 → Fin 140 :=
![
  107, 108, 76, 77, 58, 78, 79, 80, 59, 81
]
def oldChunk8 : Fin 10 → Fin 140 :=
![
  82, 36, 37, 38, 83, 84, 39, 40, 41, 42
]
def oldChunk9 : Fin 10 → Fin 140 :=
![
  99, 43, 44, 45, 85, 109, 110, 111, 112, 113
]
def oldChunk10 : Fin 10 → Fin 140 :=
![
  114, 115, 116, 100, 117, 118, 119, 101, 120, 121
]
def oldChunk11 : Fin 10 → Fin 140 :=
![
  46, 47, 48, 49, 50, 51, 52, 90, 91, 92
]
def oldChunk12 : Fin 10 → Fin 140 :=
![
  93, 94, 95, 134, 122, 135, 136, 137, 123, 138
]
def oldChunk13 : Fin 1 → Fin 140 :=
![
  139
]

def oldIndex (i : Fin 131) : Fin 140 :=
  if h : i.val < 10 then oldChunk0 ⟨i.val, by omega⟩
  else if h : i.val < 20 then oldChunk1 ⟨i.val - 10, by omega⟩
  else if h : i.val < 30 then oldChunk2 ⟨i.val - 20, by omega⟩
  else if h : i.val < 40 then oldChunk3 ⟨i.val - 30, by omega⟩
  else if h : i.val < 50 then oldChunk4 ⟨i.val - 40, by omega⟩
  else if h : i.val < 60 then oldChunk5 ⟨i.val - 50, by omega⟩
  else if h : i.val < 70 then oldChunk6 ⟨i.val - 60, by omega⟩
  else if h : i.val < 80 then oldChunk7 ⟨i.val - 70, by omega⟩
  else if h : i.val < 90 then oldChunk8 ⟨i.val - 80, by omega⟩
  else if h : i.val < 100 then oldChunk9 ⟨i.val - 90, by omega⟩
  else if h : i.val < 110 then oldChunk10 ⟨i.val - 100, by omega⟩
  else if h : i.val < 120 then oldChunk11 ⟨i.val - 110, by omega⟩
  else if h : i.val < 130 then oldChunk12 ⟨i.val - 120, by omega⟩
  else oldChunk13 ⟨i.val - 130, by omega⟩

def vertexIndex : Fin 45 → Fin 140 :=
![
  3, 4, 9, 10, 11, 12, 6, 7, 13, 53, 54, 55, 56, 57, 84,
  59, 86, 87, 89, 96, 97, 129, 130, 131, 88, 95, 60, 64, 65, 82,
  132, 98, 99, 123, 101, 124, 125, 127, 133, 126, 139, 102, 106, 107, 121
]

def select : Fin 140 → Fin 176 :=
![
  0, 1, 2, 3, 5, 6, 7, 9, 10, 11, 12, 13, 14, 15, 16,
  17, 18, 19, 20, 21, 28, 29, 30, 31, 32, 33, 34, 38, 48, 49,
  50, 51, 53, 54, 55, 56, 81, 82, 83, 86, 87, 88, 89, 91, 92,
  93, 110, 111, 112, 113, 114, 115, 116, 140, 141, 142, 143, 52, 74, 78,
  4, 22, 23, 24, 25, 26, 27, 57, 58, 59, 60, 61, 62, 63, 64,
  65, 72, 73, 75, 76, 77, 79, 80, 84, 85, 94, 147, 35, 36, 37,
  117, 118, 119, 120, 121, 122, 150, 151, 162, 90, 103, 107, 8, 66, 67,
  68, 69, 70, 71, 95, 96, 97, 98, 99, 100, 101, 102, 104, 105, 106,
  108, 109, 124, 128, 166, 39, 40, 41, 42, 43, 44, 45, 46, 47, 123,
  125, 126, 127, 129, 130
]

open BassMOuterJoin
theorem source_plus_index (i : Fin 5) :
    vertexIndex (BassMOuterJoin.sourcePlusIndex i) =
      oldIndex (BassMOuterJoin.oldSourcePlusIndex i) := by
  fin_cases i <;> decide

theorem source_middle_index (i : Fin 5) :
    vertexIndex (BassMOuterJoin.sourceMiddleIndex i) =
      oldIndex (BassMOuterJoin.oldSourceMiddleIndex i) := by
  fin_cases i <;> decide

theorem source_minus_index (i : Fin 5) :
    vertexIndex (BassMOuterJoin.sourceMinusIndex i) =
      oldIndex (BassMOuterJoin.oldSourceMinusIndex i) := by
  fin_cases i <;> decide

theorem boundary_side_plus_index (i : Fin 3) :
    vertexIndex (BassMOuterJoin.sidePlusIndex i) =
      oldIndex (BassMOuterJoin.oldSidePlusIndex i) := by
  fin_cases i <;> decide

theorem boundary_side_minus_index (i : Fin 3) :
    vertexIndex (BassMOuterJoin.sideMinusIndex i) =
      oldIndex (BassMOuterJoin.oldSideMinusIndex i) := by
  fin_cases i <;> decide

theorem boundary_first_plus_index (i : Fin 5) :
    vertexIndex (BassMOuterJoin.targetFirstPlusIndex i) =
      oldIndex (BassMOuterJoin.oldTargetFirstPlusIndex i) := by
  fin_cases i <;> decide

theorem boundary_first_minus_index (i : Fin 5) :
    vertexIndex (BassMOuterJoin.targetFirstMinusIndex i) =
      oldIndex (BassMOuterJoin.oldTargetFirstMinusIndex i) := by
  fin_cases i <;> decide

theorem boundary_second_plus_index (i : Fin 5) :
    vertexIndex (BassMOuterJoin.targetSecondPlusIndex i) =
      oldIndex (BassMOuterJoin.oldTargetSecondPlusIndex i) := by
  fin_cases i <;> decide

theorem boundary_second_minus_index (i : Fin 5) :
    vertexIndex (BassMOuterJoin.targetSecondMinusIndex i) =
      oldIndex (BassMOuterJoin.oldTargetSecondMinusIndex i) := by
  fin_cases i <;> decide

theorem boundary_middle_index (i : Fin 5) :
    vertexIndex (BassMOuterJoin.targetMiddleIndex i) =
      oldIndex (BassMOuterJoin.oldTargetMiddleIndex i) := by
  fin_cases i <;> decide

theorem oldOldPlus_monotone (i : Fin 3) :
    Monotone (oldIndex ∘ BassH1Order.oldIndex ∘
      (BassSupportOrder.oldPlusFace i).toOrderHom) := by
  fin_cases i <;> decide

theorem oldOldMinus_monotone (i : Fin 3) :
    Monotone (oldIndex ∘ BassH1Order.oldIndex ∘
      (BassSupportOrder.oldMinusFace i).toOrderHom) := by
  fin_cases i <;> decide

theorem oldH0Plus_monotone (i : Fin 3) :
    Monotone (oldIndex ∘ BassH1Order.oldIndex ∘
      (BassSupportOrder.h0PlusFace i).toOrderHom) := by
  fin_cases i <;> decide

theorem oldH0Minus_monotone (i : Fin 3) :
    Monotone (oldIndex ∘ BassH1Order.oldIndex ∘
      (BassSupportOrder.h0MinusFace i).toOrderHom) := by
  fin_cases i <;> decide

theorem oldBottom_monotone :
    Monotone (oldIndex ∘ BassH1Order.oldIndex ∘
      BassSupportOrder.bottomFace.toOrderHom) := by
  decide

theorem oldFirstPlus_monotone (i : Fin 3) :
    Monotone (oldIndex ∘ BassH1Order.firstIndex ∘
      (BassPrimitiveSupport.rectangleFace i ≫ BassH0Diagram.plusFace).toOrderHom) := by
  fin_cases i <;> decide

theorem oldFirstMinus_monotone (i : Fin 3) :
    Monotone (oldIndex ∘ BassH1Order.firstIndex ∘
      (BassPrimitiveSupport.rectangleFace i ≫ BassH0Diagram.minusFace).toOrderHom) := by
  fin_cases i <;> decide

theorem oldMiddlePlus_monotone (i : Fin 3) :
    Monotone (oldIndex ∘ BassH1Order.middleIndex ∘
      (BassPrimitiveSupport.rectangleFace i ≫ BassH0Diagram.plusFace).toOrderHom) := by
  fin_cases i <;> decide

theorem oldMiddleMinus_monotone (i : Fin 3) :
    Monotone (oldIndex ∘ BassH1Order.middleIndex ∘
      (BassPrimitiveSupport.rectangleFace i ≫ BassH0Diagram.minusFace).toOrderHom) := by
  fin_cases i <;> decide

theorem oldPlusProduct_monotone (i j : Fin 4) :
    Monotone (oldIndex ∘ BassH1Order.plusProductIndex ∘
      (BassH1Support.edgePairFace i j).toOrderHom) := by
  fin_cases i <;> fin_cases j <;> decide

theorem oldMinusProduct_monotone (i j : Fin 4) :
    Monotone (oldIndex ∘ BassH1Order.minusProductIndex ∘
      (BassH1Support.edgePairFace i j).toOrderHom) := by
  fin_cases i <;> fin_cases j <;> decide

theorem vertexPlus_monotone (i : Fin 3) :
    Monotone (vertexIndex ∘ BassMVertexOrder.plusIndex ∘
      (BassPrimitiveSupport.rectangleFace i).toOrderHom) := by
  fin_cases i <;> decide

theorem vertexMinus_monotone (i : Fin 3) :
    Monotone (vertexIndex ∘ BassMVertexOrder.minusIndex ∘
      (BassPrimitiveSupport.rectangleFace i).toOrderHom) := by
  fin_cases i <;> decide

theorem vertexMiddle_monotone (i : Fin 2) (j : Fin 4) :
    Monotone (vertexIndex ∘ BassMVertexOrder.middleIndex ∘
      (BassMPrimitiveSupport.middleEdgePairFace i j).toOrderHom) := by
  fin_cases i <;> fin_cases j <;> decide

end Quillen.PerfectComplexes.BassMWholeOrder
