/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Topology.LocalCoefficients.PeriodicSquare
public import Quillen.Topology.LocalCoefficients.SingularBar
public import Quillen.Aglib.RepresentationTheory.Homological.GroupHomology.Torus

/-!
# Calibration of the oriented periodic square in original integral bar homology

The original chains, signs, maps, basepoints and stated hypotheses are retained.
-/
@[expose] public section

section

open groupHomology.IntegralBar
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory Limits Convexity
open scoped Simplicial
namespace Quillen.LocalCoefficients.SingularBar
variable {P : Type u} [TopologicalSpace P]
open groupHomology.IntegralBar

variable [PathConnectedSpace P]

/-- The first consecutive lower label is the inverse original horizontal axis class. -/
theorem lower_label01 (σ : C(unitInterval × unitInterval, P))
    (hFirst : ∀ t, σ (0, t) = σ (1, t)) :
    label (σ (0, 0)) (lowerTriangle σ) 0 1 = (firstAxisClass σ hFirst)⁻¹ :=
  label_of_forwardPath _ _ _ _ (firstAxis σ hFirst) (lowerTriangle_edge01 σ)

/-- The second consecutive lower label is the inverse original vertical axis class. -/
theorem lower_label12 (σ : C(unitInterval × unitInterval, P))
    (hFirst : ∀ t, σ (0, t) = σ (1, t)) (hSecond : ∀ t, σ (t, 0) = σ (t, 1)) :
    label (σ (0, 0)) (lowerTriangle σ) 1 2 = (secondAxisClass σ hSecond)⁻¹ :=
  label_of_forwardPath _ _ _ _ (secondAxis σ hSecond)
    (fun t ↦ (lowerTriangle_edge12 σ t).trans (hFirst t).symm)

/-- The first consecutive upper label is the inverse original vertical axis class. -/
theorem upper_label01 (σ : C(unitInterval × unitInterval, P))
    (hSecond : ∀ t, σ (t, 0) = σ (t, 1)) :
    label (σ (0, 0)) (upperTriangle σ) 0 1 = (secondAxisClass σ hSecond)⁻¹ :=
  label_of_forwardPath _ _ _ _ (secondAxis σ hSecond) (upperTriangle_edge01 σ)

/-- The second consecutive upper label is the inverse original horizontal axis class. -/
theorem upper_label12 (σ : C(unitInterval × unitInterval, P))
    (hFirst : ∀ t, σ (0, t) = σ (1, t)) (hSecond : ∀ t, σ (t, 0) = σ (t, 1)) :
    label (σ (0, 0)) (upperTriangle σ) 1 2 = (firstAxisClass σ hFirst)⁻¹ :=
  label_of_forwardPath _ _ _ _ (firstAxis σ hFirst)
    (fun t ↦ (upperTriangle_edge12 σ t).trans (hSecond t).symm)

/-- Both diagonal labels are the inverse class of the same original diagonal path. -/
theorem diagonal_labels_eq (σ : C(unitInterval × unitInterval, P))
    (hFirst : ∀ t, σ (0, t) = σ (1, t)) (hSecond : ∀ t, σ (t, 0) = σ (t, 1)) :
    label (σ (0, 0)) (lowerTriangle σ) 0 2 = label (σ (0, 0)) (upperTriangle σ) 0 2 := by
  rw [label_of_forwardPath (σ (0, 0)) (lowerTriangle σ) 0 2
      (diagonalPath σ hFirst hSecond) (lowerTriangle_edge02 σ),
    label_of_forwardPath (σ (0, 0)) (upperTriangle σ) 0 2
      (diagonalPath σ hFirst hSecond) (upperTriangle_edge02 σ)]

/-- The original two axis classes commute, by their actual common simplex diagonal. -/
theorem axisClasses_commute (σ : C(unitInterval × unitInterval, P))
    (hFirst : ∀ t, σ (0, t) = σ (1, t)) (hSecond : ∀ t, σ (t, 0) = σ (t, 1)) :
    Commute (firstAxisClass σ hFirst) (secondAxisClass σ hSecond) := by
  have hl := label_mul (σ (0, 0)) (lowerTriangle σ) 0 1 2
  have hu := label_mul (σ (0, 0)) (upperTriangle σ) 0 1 2
  rw [lower_label01 σ hFirst, lower_label12 σ hFirst hSecond] at hl
  rw [upper_label01 σ hSecond, upper_label12 σ hFirst hSecond] at hu
  have hi : Commute (firstAxisClass σ hFirst)⁻¹ (secondAxisClass σ hSecond)⁻¹ :=
    hl.trans ((diagonal_labels_eq σ hFirst hSecond).trans hu.symm)
  simpa only [inv_inv] using hi.inv_inv

/-- The literal oriented chain maps to the simultaneous-inverse bar torus, with positive sign. -/
theorem twoMap_squareTwoChain (σ : C(unitInterval × unitInterval, P))
    (hFirst : ∀ t, σ (0, t) = σ (1, t)) (hSecond : ∀ t, σ (t, 0) = σ (t, 1)) :
    twoMap (σ (0, 0)) (squareTwoChain σ) =
      (torusCycle (ULift.{u} ℤ) (HomotopyGroup.Pi 1 P (σ (0, 0)))
        (firstAxisClass σ hFirst)⁻¹ (secondAxisClass σ hSecond)⁻¹
          (axisClasses_commute σ hFirst hSecond).inv_inv).val := by
  rw [squareTwoChain, map_sub, twoMap_inclusion, twoMap_inclusion,
    lower_label01 σ hFirst, lower_label12 σ hFirst hSecond,
    upper_label01 σ hSecond, upper_label12 σ hFirst hSecond]
  simp only [one_smul, torusCycle]

/-- The exact original square class maps to the positive original bar torus class of its axes. -/
theorem hTwoMap_squareTwoCycle (σ : C(unitInterval × unitInterval, P))
    (hFirst : ∀ t, σ (0, t) = σ (1, t)) (hSecond : ∀ t, σ (t, 0) = σ (t, 1)) :
    hTwoMap (σ (0, 0))
      ((singularChainComplex (constant P integralCoefficientModule.{u})).homologyπ 2
        (squareTwoCycle σ hFirst hSecond)) =
      integerBarCycleClass (HomotopyGroup.Pi 1 P (σ (0, 0)))
        (torusCycle (ULift.{u} ℤ) (HomotopyGroup.Pi 1 P (σ (0, 0)))
          (firstAxisClass σ hFirst) (secondAxisClass σ hSecond)
            (axisClasses_commute σ hFirst hSecond)) := by
  rw [← torusCycle_class_inv_inv, hTwoMap_class]
  change (integerBarShortComplex (HomotopyGroup.Pi 1 P (σ (0, 0)))).homologyπ _ =
    (integerBarShortComplex (HomotopyGroup.Pi 1 P (σ (0, 0)))).homologyπ _
  congr 1
  apply (ModuleCat.mono_iff_injective
    (integerBarShortComplex (HomotopyGroup.Pi 1 P (σ (0, 0)))).iCycles).mp inferInstance
  rw [hTwoMap_cycle_val, iCycles_squareTwoCycle, twoMap_squareTwoChain]
  exact ((integerBarShortComplex (HomotopyGroup.Pi 1 P (σ (0, 0)))).i_cyclesMk _ _).symm

end Quillen.LocalCoefficients.SingularBar

end
