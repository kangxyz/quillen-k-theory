/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeInputNodes
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeOrder

/-! The certified representative data in a lookup that stays within default recursion depth. -/
@[expose] public section
set_option autoImplicit false
namespace Quillen.PerfectComplexes.BassMWholeOrder

/-- Representative input slots for common-order labels 0 through 9, used by `selection`. -/
def selectionChunk0 : Fin 10 → Fin 176 :=
  ![0, 1, 2, 3, 5, 6, 7, 9, 10, 11]

/-- Representative input slots for common-order labels 10 through 19, used by `selection`. -/
def selectionChunk1 : Fin 10 → Fin 176 :=
  ![12, 13, 14, 15, 16, 17, 18, 19, 20, 21]

/-- Representative input slots for common-order labels 20 through 29, used by `selection`. -/
def selectionChunk2 : Fin 10 → Fin 176 :=
  ![28, 29, 30, 31, 32, 33, 34, 38, 48, 49]

/-- Representative input slots for common-order labels 30 through 39, used by `selection`. -/
def selectionChunk3 : Fin 10 → Fin 176 :=
  ![50, 51, 53, 54, 55, 56, 81, 82, 83, 86]

/-- Representative input slots for common-order labels 40 through 49, used by `selection`. -/
def selectionChunk4 : Fin 10 → Fin 176 :=
  ![87, 88, 89, 91, 92, 93, 110, 111, 112, 113]

/-- Representative input slots for common-order labels 50 through 59, used by `selection`. -/
def selectionChunk5 : Fin 10 → Fin 176 :=
  ![114, 115, 116, 140, 141, 142, 143, 52, 74, 78]

/-- Representative input slots for common-order labels 60 through 69, used by `selection`. -/
def selectionChunk6 : Fin 10 → Fin 176 :=
  ![4, 22, 23, 24, 25, 26, 27, 57, 58, 59]

/-- Representative input slots for common-order labels 70 through 79, used by `selection`. -/
def selectionChunk7 : Fin 10 → Fin 176 :=
  ![60, 61, 62, 63, 64, 65, 72, 73, 75, 76]

/-- Representative input slots for common-order labels 80 through 89, used by `selection`. -/
def selectionChunk8 : Fin 10 → Fin 176 :=
  ![77, 79, 80, 84, 85, 94, 147, 35, 36, 37]

/-- Representative input slots for common-order labels 90 through 99, used by `selection`. -/
def selectionChunk9 : Fin 10 → Fin 176 :=
  ![117, 118, 119, 120, 121, 122, 150, 151, 162, 90]

/-- Representative input slots for common-order labels 100 through 109, used by `selection`. -/
def selectionChunk10 : Fin 10 → Fin 176 :=
  ![103, 107, 8, 66, 67, 68, 69, 70, 71, 95]

/-- Representative input slots for common-order labels 110 through 119, used by `selection`. -/
def selectionChunk11 : Fin 10 → Fin 176 :=
  ![96, 97, 98, 99, 100, 101, 102, 104, 105, 106]

/-- Representative input slots for common-order labels 120 through 129, used by `selection`. -/
def selectionChunk12 : Fin 10 → Fin 176 :=
  ![108, 109, 124, 128, 166, 39, 40, 41, 42, 43]

/-- Representative input slots for common-order labels 130 through 139, used by `selection`. -/
def selectionChunk13 : Fin 10 → Fin 176 :=
  ![44, 45, 46, 47, 123, 125, 126, 127, 129, 130]

/-- The unchanged certificate representatives, grouped to avoid deep vector reduction. -/
def selection (i : Fin 140) : Fin 176 :=
  if h : i.val < 10 then selectionChunk0 ⟨i.val, by omega⟩
  else if h : i.val < 20 then selectionChunk1 ⟨i.val - 10, by omega⟩
  else if h : i.val < 30 then selectionChunk2 ⟨i.val - 20, by omega⟩
  else if h : i.val < 40 then selectionChunk3 ⟨i.val - 30, by omega⟩
  else if h : i.val < 50 then selectionChunk4 ⟨i.val - 40, by omega⟩
  else if h : i.val < 60 then selectionChunk5 ⟨i.val - 50, by omega⟩
  else if h : i.val < 70 then selectionChunk6 ⟨i.val - 60, by omega⟩
  else if h : i.val < 80 then selectionChunk7 ⟨i.val - 70, by omega⟩
  else if h : i.val < 90 then selectionChunk8 ⟨i.val - 80, by omega⟩
  else if h : i.val < 100 then selectionChunk9 ⟨i.val - 90, by omega⟩
  else if h : i.val < 110 then selectionChunk10 ⟨i.val - 100, by omega⟩
  else if h : i.val < 120 then selectionChunk11 ⟨i.val - 110, by omega⟩
  else if h : i.val < 130 then selectionChunk12 ⟨i.val - 120, by omega⟩
  else selectionChunk13 ⟨i.val - 130, by omega⟩

/-- Every original old input is its own actual selected representative. -/
theorem selection_old (i : Fin 131) : selection (oldIndex i) = Fin.castAdd 45 i := by
  fin_cases i <;> rfl

/--
Representative input slots for merged M vertices 0 through 9, used by `vertexRepresentative`.
-/
def vertexRepChunk0 : Fin 10 → Fin 176 :=
  ![3, 5, 11, 12, 13, 14, 7, 9, 15, 140]

/--
Representative input slots for merged M vertices 10 through 19, used by `vertexRepresentative`.
-/
def vertexRepChunk1 : Fin 10 → Fin 176 :=
  ![141, 142, 143, 52, 85, 78, 147, 35, 37, 150]

/--
Representative input slots for merged M vertices 20 through 29, used by `vertexRepresentative`.
-/
def vertexRepChunk2 : Fin 10 → Fin 176 :=
  ![151, 43, 44, 45, 36, 122, 4, 25, 26, 80]

/--
Representative input slots for merged M vertices 30 through 39, used by `vertexRepresentative`.
-/
def vertexRepChunk3 : Fin 10 → Fin 176 :=
  ![46, 162, 90, 128, 107, 166, 39, 41, 47, 40]

/-- Representative input slots for the final five merged M vertices, numbered 40 through 44. -/
def vertexRepChunk4 : Fin 5 → Fin 176 :=
  ![130, 8, 69, 70, 109]

/-- The actual selected M slots, grouped only to keep reduction within the default depth. -/
def vertexRepresentative (i : Fin 45) : Fin 176 :=
  if h : i.val < 10 then vertexRepChunk0 ⟨i.val, by omega⟩
  else if h : i.val < 20 then vertexRepChunk1 ⟨i.val - 10, by omega⟩
  else if h : i.val < 30 then vertexRepChunk2 ⟨i.val - 20, by omega⟩
  else if h : i.val < 40 then vertexRepChunk3 ⟨i.val - 30, by omega⟩
  else vertexRepChunk4 ⟨i.val - 40, by omega⟩

theorem selection_vertex_chunk0 (i : Fin 10) :
    selection (vertexIndex ⟨i.val, by omega⟩) =
      vertexRepresentative ⟨i.val, by omega⟩ := by
  fin_cases i <;> decide

theorem selection_vertex_chunk1 (i : Fin 10) :
    selection (vertexIndex ⟨i.val + 10, by omega⟩) =
      vertexRepresentative ⟨i.val + 10, by omega⟩ := by
  fin_cases i <;> decide

theorem selection_vertex_chunk2 (i : Fin 10) :
    selection (vertexIndex ⟨i.val + 20, by omega⟩) =
      vertexRepresentative ⟨i.val + 20, by omega⟩ := by
  fin_cases i <;> decide

theorem selection_vertex_chunk3 (i : Fin 10) :
    selection (vertexIndex ⟨i.val + 30, by omega⟩) =
      vertexRepresentative ⟨i.val + 30, by omega⟩ := by
  fin_cases i <;> decide

theorem selection_vertex_chunk4 (i : Fin 5) :
    selection (vertexIndex ⟨i.val + 40, by omega⟩) =
      vertexRepresentative ⟨i.val + 40, by omega⟩ := by
  fin_cases i <;> decide

/-- Every first-stage representative is checked without enlarging the standard kernel budget. -/
theorem selection_vertex (i : Fin 45) : selection (vertexIndex i) = vertexRepresentative i := by
  fin_cases i
  · exact selection_vertex_chunk0 0
  · exact selection_vertex_chunk0 1
  · exact selection_vertex_chunk0 2
  · exact selection_vertex_chunk0 3
  · exact selection_vertex_chunk0 4
  · exact selection_vertex_chunk0 5
  · exact selection_vertex_chunk0 6
  · exact selection_vertex_chunk0 7
  · exact selection_vertex_chunk0 8
  · exact selection_vertex_chunk0 9
  · exact selection_vertex_chunk1 0
  · exact selection_vertex_chunk1 1
  · exact selection_vertex_chunk1 2
  · exact selection_vertex_chunk1 3
  · exact selection_vertex_chunk1 4
  · exact selection_vertex_chunk1 5
  · exact selection_vertex_chunk1 6
  · exact selection_vertex_chunk1 7
  · exact selection_vertex_chunk1 8
  · exact selection_vertex_chunk1 9
  · exact selection_vertex_chunk2 0
  · exact selection_vertex_chunk2 1
  · exact selection_vertex_chunk2 2
  · exact selection_vertex_chunk2 3
  · exact selection_vertex_chunk2 4
  · exact selection_vertex_chunk2 5
  · exact selection_vertex_chunk2 6
  · exact selection_vertex_chunk2 7
  · exact selection_vertex_chunk2 8
  · exact selection_vertex_chunk2 9
  · exact selection_vertex_chunk3 0
  · exact selection_vertex_chunk3 1
  · exact selection_vertex_chunk3 2
  · exact selection_vertex_chunk3 3
  · exact selection_vertex_chunk3 4
  · exact selection_vertex_chunk3 5
  · exact selection_vertex_chunk3 6
  · exact selection_vertex_chunk3 7
  · exact selection_vertex_chunk3 8
  · exact selection_vertex_chunk3 9
  · exact selection_vertex_chunk4 0
  · exact selection_vertex_chunk4 1
  · exact selection_vertex_chunk4 2
  · exact selection_vertex_chunk4 3
  · exact selection_vertex_chunk4 4

end Quillen.PerfectComplexes.BassMWholeOrder
