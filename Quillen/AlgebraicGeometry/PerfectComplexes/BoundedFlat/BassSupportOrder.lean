/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassPrimitiveSupport

/-! Kernel-checked scalar indexing for the thirteen actually supported faces.
No equality of coefficient reference nodes is asserted by this finite indexing result. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory Convexity Quillen.SimplexParameters
open scoped Simplicial Topology unitInterval
namespace Quillen.PerfectComplexes.BassSupportOrder
open BassPrimitiveSupport

/-- Scalar reindexing of the old 45 slots; monotonicity is required only on actual supports. -/
def oldIndex : Fin 45 → Fin 63 := ![
    21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35,
    16, 17, 18, 19, 36, 37, 38, 39, 40, 43, 44, 45, 46, 47, 48,
    49, 50, 51, 52, 53, 54, 55, 56, 57, 41, 58, 59, 60, 61, 62]

/-- Scalar reindexing of H0's 31 slots, retaining the thirteen specified shared edge labels. -/
def h0Index : Fin 31 → Fin 63 := ![
    0, 1, 16, 19, 2, 3, 4, 5, 20, 21, 35, 38, 22, 23, 41,
    6, 7, 8, 9, 42, 43, 57, 60, 44, 45, 10, 11, 12, 13, 14,
    15]

/-- All thirteen paired scalar labels agree literally. This does not identify their references. -/
theorem paired_indices (i : Fin 13) :
    h0Index (![2, 3, 9, 10, 11, 12, 13, 14, 20, 21, 22, 23, 24] i) =
      oldIndex (![15, 18, 0, 14, 21, 1, 2, 39, 24, 38, 42, 25, 26] i) := by
  fin_cases i <;> rfl

/-- Each of these three original whole seven-faces retains its native order. -/
theorem oldPlus_monotone (i : Fin 3) :
    Monotone (oldIndex ∘
      (rectangleFace i ≫ (BassOverlap.plusFace ≫ BassReferenceMerge.chartFace)).toOrderHom) := by
  fin_cases i <;> decide

def oldPlusFace (i : Fin 3) : ⦋7⦌ ⟶ ⦋62⦌ :=
  SimplexCategory.Hom.mk ⟨oldIndex ∘ (rectangleFace i ≫
    (BassOverlap.plusFace ≫ BassReferenceMerge.chartFace)).toOrderHom, oldPlus_monotone i⟩

/-- Each of these three original whole seven-faces retains its native order. -/
theorem oldMinus_monotone (i : Fin 3) :
    Monotone (oldIndex ∘
      (rectangleFace i ≫ (BassOverlap.minusFace ≫ BassReferenceMerge.chartFace)).toOrderHom) := by
  fin_cases i <;> decide

def oldMinusFace (i : Fin 3) : ⦋7⦌ ⟶ ⦋62⦌ :=
  SimplexCategory.Hom.mk ⟨oldIndex ∘ (rectangleFace i ≫
    (BassOverlap.minusFace ≫ BassReferenceMerge.chartFace)).toOrderHom, oldMinus_monotone i⟩

/-- Each of these three original whole seven-faces retains its native order. -/
theorem h0Plus_monotone (i : Fin 3) :
    Monotone (h0Index ∘ (rectangleFace i ≫ (BassH0Diagram.plusFace)).toOrderHom) := by
  fin_cases i <;> decide

def h0PlusFace (i : Fin 3) : ⦋7⦌ ⟶ ⦋62⦌ :=
  SimplexCategory.Hom.mk ⟨h0Index ∘ (rectangleFace i ≫
    (BassH0Diagram.plusFace)).toOrderHom, h0Plus_monotone i⟩

/-- Each of these three original whole seven-faces retains its native order. -/
theorem h0Minus_monotone (i : Fin 3) :
    Monotone (h0Index ∘ (rectangleFace i ≫ (BassH0Diagram.minusFace)).toOrderHom) := by
  fin_cases i <;> decide

def h0MinusFace (i : Fin 3) : ⦋7⦌ ⟶ ⦋62⦌ :=
  SimplexCategory.Hom.mk ⟨h0Index ∘ (rectangleFace i ≫
    (BassH0Diagram.minusFace)).toOrderHom, h0Minus_monotone i⟩

/-- The complete original bottom fourteen-simplex also retains its order. -/
theorem bottom_monotone : Monotone (oldIndex ∘ BassReferenceMerge.bottomFace.toOrderHom) := by
  decide

def bottomFace : ⦋14⦌ ⟶ ⦋62⦌ :=
  SimplexCategory.Hom.mk ⟨oldIndex ∘ BassReferenceMerge.bottomFace.toOrderHom, bottom_monotone⟩

end Quillen.PerfectComplexes.BassSupportOrder
