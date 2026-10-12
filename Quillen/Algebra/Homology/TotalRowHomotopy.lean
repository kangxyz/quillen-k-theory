/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Algebra.Homology.TotalComplexCoordinates
public import Quillen.Algebra.Homology.TotalSingle
public import Mathlib.Algebra.Homology.Homotopy

/-! # Signed row homotopies on the actual first-quadrant total complex -/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Quillen.HomologicalAlgebra

variable (K : HomologicalComplex₂ (ModuleCat.{u} ℤ)
  (ComplexShape.down ℕ) (ComplexShape.down ℕ))

/-- A family of row homotopies, without any compatibility in the outer direction. -/
abbrev RowHomotopyData := ∀ i p q, (K.X i).X p ⟶ (K.X i).X q

variable (h : RowHomotopyData K)

/-- The signed degree-one map induced on the original total summands. -/
def totalRowHomotopySucc (n : ℕ) :
    (K.total (ComplexShape.down ℕ)).X n ⟶ (K.total (ComplexShape.down ℕ)).X (n + 1) :=
  K.totalDesc fun i p hip ↦ (ComplexShape.down ℕ).ε i •
    (h i p (p + 1) ≫ K.ιTotal (ComplexShape.down ℕ) i (p + 1) (n + 1)
      (by change i + (p + 1) = n + 1; change i + p = n at hip; omega))

/-- The same maps as a degree-indexed homotopy family, zero in other degrees. -/
def totalRowHomotopy (n m : ℕ) :
    (K.total (ComplexShape.down ℕ)).X n ⟶ (K.total (ComplexShape.down ℕ)).X m :=
  if hm : n + 1 = m then hm ▸ totalRowHomotopySucc K h n else 0

@[simp]
theorem totalRowHomotopy_succ (n : ℕ) :
    totalRowHomotopy K h n (n + 1) = totalRowHomotopySucc K h n := by
  simp [totalRowHomotopy]

theorem totalRowHomotopy_zero (n m : ℕ) (hm : ¬(ComplexShape.down ℕ).Rel m n) :
    totalRowHomotopy K h n m = 0 := by
  simp [totalRowHomotopy, show n + 1 ≠ m from hm]

/-- Removing the null-homotopic signed row operator gives an actual chain map. -/
def totalRowDefect : K.total (ComplexShape.down ℕ) ⟶ K.total (ComplexShape.down ℕ) :=
  𝟙 _ - Homotopy.nullHomotopicMap (totalRowHomotopy K h)

/-- The defect always induces the identity on homology. -/
def totalRowDefectHomotopy :
    Homotopy (𝟙 _) (totalRowDefect K h) where
  hom := totalRowHomotopy K h
  zero := totalRowHomotopy_zero K h
  comm n := by
    change 𝟙 _ = dNext n (totalRowHomotopy K h) +
      prevD n (totalRowHomotopy K h) +
      (𝟙 _ - (dNext n (totalRowHomotopy K h) + prevD n (totalRowHomotopy K h)))
    abel

@[reassoc (attr := simp)]
theorem ι_totalRowHomotopySucc (n i p : ℕ) (hip : i + p = n) :
    K.ιTotal (ComplexShape.down ℕ) i p n hip ≫ totalRowHomotopySucc K h n =
      (ComplexShape.down ℕ).ε i •
        (h i p (p + 1) ≫ K.ιTotal (ComplexShape.down ℕ) i (p + 1) (n + 1)
          (by change i + (p + 1) = n + 1; omega)) := by
  simp [totalRowHomotopySucc]

variable {K} {C : ChainComplex (ModuleCat.{u} ℤ) ℕ}
  (f : K ⟶ HomologicalComplex₂.single₀Bicomplex C)

/-- A row homotopy followed by the original augmentation is zero. -/
@[reassoc]
theorem totalRowHomotopy_augmentation (n m : ℕ) :
    totalRowHomotopy K h n m ≫
      (HomologicalComplex₂.total.map f (ComplexShape.down ℕ)).f m = 0 := by
  classical
  by_cases hm : n + 1 = m
  · subst m
    rw [totalRowHomotopy_succ]
    apply HomologicalComplex₂.total.hom_ext
    intro i p hip
    simp only [ι_totalRowHomotopySucc_assoc, Linear.units_smul_comp,
      Category.assoc, HomologicalComplex₂.ιTotal_map, comp_zero]
    have hf : (f.f i).f (p + 1) = 0 :=
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) 0 (C.X i)
        (p + 1) (by omega)).eq_of_tgt _ _
    rw [hf, zero_comp, comp_zero, smul_zero]
  · simp [totalRowHomotopy, hm]

/-- The actual total augmentation is unchanged by the defect chain map. -/
@[reassoc]
theorem totalRowDefect_augmentation :
    totalRowDefect K h ≫ HomologicalComplex₂.total.map f (ComplexShape.down ℕ) =
      HomologicalComplex₂.total.map f (ComplexShape.down ℕ) := by
  rw [totalRowDefect, Preadditive.sub_comp, Category.id_comp,
    Homotopy.nullHomotopicMap_comp]
  have hz : (fun n m ↦ totalRowHomotopy K h n m ≫
      (HomologicalComplex₂.total.map f (ComplexShape.down ℕ)).f m) = 0 := by
    funext n m
    exact totalRowHomotopy_augmentation h f n m
  rw [hz]
  have hz' : Homotopy.nullHomotopicMap
      (0 : ∀ n m, (K.total (ComplexShape.down ℕ)).X n ⟶
        ((HomologicalComplex₂.single₀Bicomplex C).total (ComplexShape.down ℕ)).X m) = 0 := by
    ext n
    simp [Homotopy.nullHomotopicMap, dNext, prevD]
  rw [hz', sub_zero]

end Quillen.HomologicalAlgebra
