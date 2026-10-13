/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Algebra.Homology.TotalRowHorizontal
public import Quillen.Algebra.Homology.TotalRowVertical
public import Quillen.Algebra.Homology.TotalRowSection
public import Quillen.Algebra.Homology.TotalTriangularComparison

/-!
# First-quadrant total comparison from actual row contractions

Independently chosen contractions onto inner degree zero suffice. Their signed
sum gives a genuine total homotopy. Its defect fixes the original augmentation
and strictly lowers the finite outer support on the augmentation kernel.
-/

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

/-- The two total differential directions give exactly the signed homotopy boundary. -/
theorem totalRowDefect_f (h : RowHomotopyData K) (n : ℕ) :
    (totalRowDefect K h).f n =
      𝟙 _ - (totalRowHorizontal K h n + totalRowVertical K h n) := by
  dsimp [totalRowDefect, Homotopy.nullHomotopicMap, dNext, prevD,
    totalRowHorizontal, totalRowVertical, HomologicalComplex₂.total]
  simp only [Preadditive.add_comp, Preadditive.comp_add]
  congr 1
  abel


variable {K}

/-- The diagonal row projector factors through the original total augmentation. -/
theorem totalRowProjector_eq_map_section
    {L : HomologicalComplex₂ (ModuleCat.{u} ℤ)
      (ComplexShape.down ℕ) (ComplexShape.down ℕ)}
    (f : K ⟶ L) (s : ∀ i, L.X i ⟶ K.X i) (n : ℕ) :
    totalRowProjector K (fun i ↦ f.f i ≫ s i) n =
      (HomologicalComplex₂.total.map f (ComplexShape.down ℕ)).f n ≫ totalRowSection s n := by
  apply HomologicalComplex₂.total.hom_ext
  intro i p hip
  rw [ι_totalRowProjector, HomologicalComplex₂.ιTotal_map_assoc, ι_totalRowSection]
  exact Category.assoc _ _ _

/-- Actual row contractions onto inner degree zero imply that the original first-quadrant
augmentation is a quasi-isomorphism. No outer naturality or convergence hypothesis is needed. -/
theorem total_quasiIso_of_row_contractions
    {C : ChainComplex (ModuleCat.{u} ℤ) ℕ}
    (f : K ⟶ HomologicalComplex₂.single₀Bicomplex C)
    (s : ∀ i, (HomologicalComplex₂.single₀Bicomplex C).X i ⟶ K.X i)
    (hs : ∀ i, s i ≫ f.f i = 𝟙 _)
    (h : ∀ i, Homotopy (𝟙 (K.X i)) (f.f i ≫ s i)) :
    QuasiIso (HomologicalComplex₂.total.map f (ComplexShape.down ℕ)) := by
  let H : RowHomotopyData K := fun i ↦ (h i).hom
  apply quasiIso_of_total_triangular
    (HomologicalComplex₂.total.map f (ComplexShape.down ℕ))
    (totalRowSection s) (totalRowSection_map s f hs)
    (totalRowDefect K H) (totalRowDefectHomotopy K H)
    (totalRowDefect_augmentation H f)
  intro n p q hpq
  have heq : (totalRowDefect K H).f n -
      (HomologicalComplex₂.total.map f (ComplexShape.down ℕ)).f n ≫ totalRowSection s n =
        -totalRowHorizontal K H n := by
    rw [totalRowDefect_f, ← totalRowProjector_eq_map_section f s n]
    change 𝟙 _ - (totalRowHorizontal K H n +
      totalRowVertical K (fun i ↦ (h i).hom) n) - _ = _
    rw [totalRowVertical_eq]
    abel
  rw [heq, Preadditive.neg_comp, Preadditive.comp_neg,
    totalRowHorizontal_lower K H n p q hpq, neg_zero]

end Quillen.HomologicalAlgebra
