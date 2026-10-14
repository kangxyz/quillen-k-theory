/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MInternalFaces

/-! Actual first-stage component ordering after the proved full internal node identities. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory
open scoped Simplicial
namespace Quillen.PerfectComplexes.BassMVertexOrder

def plusIndex : Fin 18 → Fin 45 :=
  ![0, 1, 4, 11, 12, 13, 14, 15, 16, 17, 18, 23, 24, 25, 26, 27, 28, 29]

def plusFace : ⦋17⦌ ⟶ ⦋44⦌ :=
  SimplexCategory.Hom.mk ⟨plusIndex, by decide⟩

def middleIndex : Fin 15 → Fin 45 :=
  ![2, 3, 4, 5, 8, 9, 10, 11, 19, 20, 21, 22, 23, 30, 38]

def middleFace : ⦋14⦌ ⟶ ⦋44⦌ :=
  SimplexCategory.Hom.mk ⟨middleIndex, by decide⟩

def minusIndex : Fin 18 → Fin 45 :=
  ![6, 7, 8, 20, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44]

def minusFace : ⦋17⦌ ⟶ ⦋44⦌ :=
  SimplexCategory.Hom.mk ⟨minusIndex, by decide⟩

def select : Fin 45 → Fin 51 :=
  ![0, 1, 18, 19, 2, 21, 33, 34, 22, 23, 24, 3, 4, 5, 6, 7, 8, 9, 10, 26, 27, 28,
    29, 11, 12, 13, 14, 15, 16, 17, 31, 37, 38, 39, 40, 41, 42, 43, 32, 45, 46, 47, 48, 49, 50]

end Quillen.PerfectComplexes.BassMVertexOrder
