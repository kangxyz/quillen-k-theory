/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Topology.LocalCoefficients.CechSplitRows
public import Quillen.Topology.LocalCoefficients.SmallChainQuasiIso
public import Quillen.Algebra.Homology.TotalRowContraction

/-!
# The actual twisted Čech total augmentation is a quasi-isomorphism

The independently constructed row contractions satisfy the proved finite
first-quadrant perturbation theorem. Their actual total augmentation is
therefore a quasi-isomorphism onto the original small-chain complex. For an
open cover, the original augmentation to all twisted singular chains is a
quasi-isomorphism as well, for every integral local coefficient system.
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

/-- The original total augmentation onto actual small chains is a quasi-isomorphism. -/
theorem cechSmallChainAugmentation_quasiIso : QuasiIso (cechSmallChainAugmentation U A) := by
  have ht := Quillen.HomologicalAlgebra.total_quasiIso_of_row_contractions
    (cechCanonicalBicomplexAugmentation U A)
    (fun n ↦ (cechRowHomotopyEquiv U A ⦋n⦌).inv)
    (cechCanonicalBicomplexAugmentation_split U A)
    (cechCanonicalBicomplexAugmentationHomotopy U A)
  have hc : QuasiIso
      (HomologicalComplex₂.total.map (cechCanonicalBicomplexAugmentation U A)
        (ComplexShape.down ℕ) ≫
        (HomologicalComplex₂.single₀TotalIso (smallChainComplex U A)).inv) := inferInstance
  rwa [cechCanonicalTotalAugmentation_eq] at hc

/-- For a genuine open cover, the original augmentation to all twisted chains is a quasi-iso. -/
theorem cechSingularAugmentation_quasiIso
    (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i) :
    QuasiIso (cechSingularAugmentation U A) := by
  have := cechSmallChainAugmentation_quasiIso U A
  have := smallChainComplexInclusion_quasiIso U hU hcover A
  exact inferInstanceAs (QuasiIso (cechSmallChainAugmentation U A ≫ smallChainComplexInclusion U A))

/-- The induced map on actual local-coefficient homology is the original augmentation map. -/
theorem cechSingularAugmentation_homology_isIso
    (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (cechSingularAugmentation U A) n) := by
  have := cechSingularAugmentation_quasiIso U A hU hcover
  infer_instance

end Quillen.LocalCoefficients
