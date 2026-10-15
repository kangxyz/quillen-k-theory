/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.H1InputNodes

/-! Explicit representatives of the checked 131-slot supported family. -/
@[expose] public section
set_option autoImplicit false
namespace Quillen.PerfectComplexes.BassH1Merged

/-- Chosen tagged representatives for slots 0 through 19 of the merged 131-node family. -/
def selectBlock0 : Fin 20 → Input := ![
  oldInput 0, oldInput 1, oldInput 2, oldInput 3, oldInput 4,
  oldInput 5, oldInput 6, oldInput 7, oldInput 8, oldInput 9,
  oldInput 10, oldInput 11, oldInput 12, oldInput 13, oldInput 14,
  oldInput 15, oldInput 16, oldInput 17, firstInput 0, firstInput 1]

/-- Chosen tagged representatives for slots 20 through 39 of the merged 131-node family. -/
def selectBlock1 : Fin 20 → Input := ![
  oldInput 18, oldInput 19, oldInput 20, oldInput 21, oldInput 22,
  oldInput 23, oldInput 24, oldInput 25, oldInput 36, oldInput 37,
  firstInput 4, firstInput 15, middleInput 0, middleInput 1, middleInput 4,
  middleInput 5, middleInput 6, middleInput 7, middleInput 15, middleInput 16]

/-- Chosen tagged representatives for slots 40 through 59 of the merged 131-node family. -/
def selectBlock2 : Fin 20 → Input := ![
  middleInput 17, middleInput 18, middleInput 25, middleInput 26, middleInput 27,
  middleInput 28, middleInput 29, middleInput 30, plusInput 0, plusInput 1,
  firstInput 5, plusInput 3, plusInput 4, plusInput 5, plusInput 6,
  firstInput 6, firstInput 8, oldInput 26, oldInput 27, oldInput 28]

/-- Chosen tagged representatives for slots 60 through 79 of the merged 131-node family. -/
def selectBlock3 : Fin 20 → Input := ![
  oldInput 29, oldInput 35, oldInput 38, oldInput 39, oldInput 40,
  oldInput 41, oldInput 42, oldInput 43, oldInput 44, oldInput 45,
  oldInput 46, oldInput 47, oldInput 58, oldInput 59, plusInput 8,
  oldInput 30, oldInput 33, oldInput 34, plusInput 9, oldInput 31]

/-- Chosen tagged representatives for slots 80 through 99 of the merged 131-node family. -/
def selectBlock4 : Fin 20 → Input := ![
  oldInput 32, plusInput 15, plusInput 16, firstInput 7, plusInput 18,
  plusInput 19, minusInput 0, minusInput 1, firstInput 16, minusInput 3,
  minusInput 4, minusInput 5, minusInput 6, firstInput 17, firstInput 19,
  oldInput 48, oldInput 49, oldInput 50, oldInput 51, oldInput 57]

/-- Chosen tagged representatives for slots 100 through 119 of the merged 131-node family. -/
def selectBlock5 : Fin 20 → Input := ![
  oldInput 60, oldInput 61, oldInput 62, minusInput 8, oldInput 52,
  oldInput 55, oldInput 56, minusInput 9, oldInput 53, oldInput 54,
  minusInput 15, minusInput 16, firstInput 18, firstInput 25, firstInput 26,
  firstInput 27, firstInput 29, middleInput 8, middleInput 9, middleInput 10]

/-- Chosen tagged representatives for the final slots 120 through 130 of the merged family. -/
def selectBlock6 : Fin 11 → Input := ![
  firstInput 28, middleInput 12, middleInput 13, middleInput 19, minusInput 18,
  middleInput 20, middleInput 21, firstInput 30, minusInput 19, middleInput 23,
  middleInput 24]

/-- Chooses the tagged input representing a merged slot by dispatching to its consecutive block. -/
def select (i : Fin 131) : Input :=
  if h0 : i.val < 20 then selectBlock0 ⟨i.val - 0, by omega⟩ else
  if h1 : i.val < 40 then selectBlock1 ⟨i.val - 20, by omega⟩ else
  if h2 : i.val < 60 then selectBlock2 ⟨i.val - 40, by omega⟩ else
  if h3 : i.val < 80 then selectBlock3 ⟨i.val - 60, by omega⟩ else
  if h4 : i.val < 100 then selectBlock4 ⟨i.val - 80, by omega⟩ else
  if h5 : i.val < 120 then selectBlock5 ⟨i.val - 100, by omega⟩ else
    selectBlock6 ⟨i.val - 120, by omega⟩

/--
Chooses representatives for the first H1 family, replacing its shared boundary inputs by old-
family inputs.
-/
def firstRepresentative : Fin 31 → Input := ![
  firstInput 0, firstInput 1, oldInput 18, oldInput 37, firstInput 4,
  firstInput 5, firstInput 6, firstInput 7, firstInput 8, oldInput 26,
  oldInput 28, oldInput 40, oldInput 27, oldInput 34, oldInput 59,
  firstInput 15, firstInput 16, firstInput 17, firstInput 18, firstInput 19,
  oldInput 48, oldInput 50, oldInput 62, oldInput 49, oldInput 56,
  firstInput 25, firstInput 26, firstInput 27, firstInput 28, firstInput 29,
  firstInput 30]

/--
Chooses representatives for the middle H1 family, using first-family inputs on their shared
path.
-/
def middleRepresentative : Fin 31 → Input := ![
  middleInput 0, middleInput 1, firstInput 26, firstInput 27, middleInput 4,
  middleInput 5, middleInput 6, middleInput 7, middleInput 8, middleInput 9,
  middleInput 10, firstInput 28, middleInput 12, middleInput 13, firstInput 29,
  middleInput 15, middleInput 16, middleInput 17, middleInput 18, middleInput 19,
  middleInput 20, middleInput 21, firstInput 30, middleInput 23, middleInput 24,
  middleInput 25, middleInput 26, middleInput 27, middleInput 28, middleInput 29,
  middleInput 30]

/--
Chooses positive chart representatives from the positive, first, middle, and old input families.
-/
def plusRepresentative : Fin 25 → Input := ![
  plusInput 0, plusInput 1, firstInput 5, plusInput 3, plusInput 4,
  plusInput 5, plusInput 6, firstInput 6, plusInput 8, plusInput 9,
  oldInput 30, oldInput 33, oldInput 34, oldInput 31, oldInput 32,
  plusInput 15, plusInput 16, firstInput 7, plusInput 18, plusInput 19,
  middleInput 9, middleInput 10, firstInput 28, middleInput 12, middleInput 13]

/--
Chooses inverse chart representatives from the inverse, first, middle, and old input families.
-/
def minusRepresentative : Fin 25 → Input := ![
  minusInput 0, minusInput 1, firstInput 16, minusInput 3, minusInput 4,
  minusInput 5, minusInput 6, firstInput 17, minusInput 8, minusInput 9,
  oldInput 52, oldInput 55, oldInput 56, oldInput 53, oldInput 54,
  minusInput 15, minusInput 16, firstInput 18, minusInput 18, minusInput 19,
  middleInput 20, middleInput 21, firstInput 30, middleInput 23, middleInput 24]

theorem select_old (i : Fin 63) :
    select (BassH1Order.oldIndex i) = oldInput i := by
  fin_cases i <;> rfl

theorem select_first (i : Fin 31) :
    select (BassH1Order.firstIndex i) = firstRepresentative i := by
  fin_cases i <;> rfl

theorem select_middle (i : Fin 31) :
    select (BassH1Order.middleIndex i) = middleRepresentative i := by
  fin_cases i <;> rfl

theorem select_plus (i : Fin 25) :
    select (BassH1Order.plusProductIndex i) = plusRepresentative i := by
  fin_cases i <;> rfl

theorem select_minus (i : Fin 25) :
    select (BassH1Order.minusProductIndex i) = minusRepresentative i := by
  fin_cases i <;> rfl

end Quillen.PerfectComplexes.BassH1Merged
