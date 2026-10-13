/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.LocalCoefficients.CechAugmentation

/-!
# Actual split contractions of the augmented Čech rows

The row inverse is a strict section of the original augmentation. We align
the bicomplex target with the canonical degree-zero concentration used in
first-quadrant total comparison. None of the chosen sections or homotopies
is assumed natural in singular degree.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits Opposite
open scoped Simplicial

universe u

namespace Quillen.LocalCoefficients

variable {X : Type u} [TopologicalSpace X] {ι : Type u}
  (U : ι → Set X) (A : System.{u, u} X)

/-- The actual row inverse is a strict section, not only a homotopy inverse. -/
@[reassoc (attr := simp)]
theorem cechRowSection_augmentation (n : SimplexCategory) :
    (cechRowHomotopyEquiv U A n).inv ≫ cechRowAugmentation U A n = 𝟙 _ := by
  apply HomologicalComplex.to_single_hom_ext
  change cechAugmentationSection U A n ≫ cechModuleAugmentation U A n ⦋0⦌ = 𝟙 _
  exact (cechRowExtraDegeneracy U A n).s'_comp_ε

/-- Canonical target alignment retains the original augmentation in each row. -/
def cechCanonicalBicomplexAugmentation : cechBicomplex U A ⟶
    HomologicalComplex₂.single₀Bicomplex (smallChainComplex U A) :=
  cechBicomplexAugmentation U A ≫ (smallSingleBicomplexIso U A).inv

@[simp]
theorem cechCanonicalBicomplexAugmentation_f (n : ℕ) :
    (cechCanonicalBicomplexAugmentation U A).f n = cechRowAugmentation U A ⦋n⦌ := by
  change cechRowAugmentation U A ⦋n⦌ ≫ (𝟙 _) = _
  exact Category.comp_id _

/-- The actual canonical bicomplex row maps have strict, independently chosen sections. -/
theorem cechCanonicalBicomplexAugmentation_split (n : ℕ) :
    (cechRowHomotopyEquiv U A ⦋n⦌).inv ≫ (cechCanonicalBicomplexAugmentation U A).f n = 𝟙 _ := by
  rw [cechCanonicalBicomplexAugmentation_f, cechRowSection_augmentation]

/-- The original row contraction in the orientation used for finite perturbation. -/
def cechCanonicalBicomplexAugmentationHomotopy (n : ℕ) :
    Homotopy (𝟙 ((cechBicomplex U A).X n))
      ((cechCanonicalBicomplexAugmentation U A).f n ≫
        (cechRowHomotopyEquiv U A ⦋n⦌).inv) := by
  rw [cechCanonicalBicomplexAugmentation_f]
  exact (cechRowHomotopyEquiv U A ⦋n⦌).homotopyHomInvId.symm

/-- Canonical target alignment preserves the original total augmentation to small chains. -/
theorem cechCanonicalTotalAugmentation_eq :
    HomologicalComplex₂.total.map (cechCanonicalBicomplexAugmentation U A) (ComplexShape.down ℕ) ≫
        (HomologicalComplex₂.single₀TotalIso (smallChainComplex U A)).inv =
      cechSmallChainAugmentation U A := by
  simp [cechCanonicalBicomplexAugmentation, cechSmallChainAugmentation, cechTotalAugmentation,
    smallSingleTotalIso, HomologicalComplex₂.total.map_comp, HomologicalComplex₂.total.mapIso,
    Category.assoc]

end Quillen.LocalCoefficients
