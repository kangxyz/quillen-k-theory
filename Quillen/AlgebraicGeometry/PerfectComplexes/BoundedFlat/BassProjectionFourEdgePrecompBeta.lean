/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassProjectionFourEdgePrecompMap

/-! Full Laurent-reference naturality of the entire original four-edge attachment. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassProjectionPath.WholeReference.FourEdge.Precomp
open BassH0Merge CommonReferenceNerve CommonReferenceNerve.CutOpenCarrier
variable {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R)
variable {U V : Model.{u + 1}} (A : U ⟶ V)
  (E : V ⟶ modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))
local notation "J" => normalizedMap (polynomialProjection P a)

/-- The first complete pushout obeys the original Laurent reference square. -/
theorem first_beta : first P a A E ≫ beta P a (A ≫ E) =
    firstMap P a E ≫ onReference A (reference P a E) := by
  apply (DoubleCylinder.simplicial_isPushout (𝟙 _) (FourEdgeTree.attachment E J)).hom_ext
  · simp only [← Category.assoc]
    change (_ ≫ first P a A E) ≫ _ = (_ ≫ firstMap P a E) ≫ _
    rw [first_cylinder, firstMap_edge, Category.assoc, beta_edge12]
    exact (edge P a A E 1 2).symm
  · apply coprod.hom_ext
    · simp only [← Category.assoc]
      change (FourEdgeTree.firstOne E J ≫ first P a A E) ≫ _ =
        (FourEdgeTree.firstOne E J ≫ firstMap P a E) ≫ _
      rw [first_one, firstMap_one, Category.assoc, beta_one]
      exact (vertex P a A E 1).symm
    · simp only [← Category.assoc]
      change (FourEdgeTree.firstPlus E J ≫ first P a A E) ≫ _ =
        (FourEdgeTree.firstPlus E J ≫ firstMap P a E) ≫ _
      rw [first_plus, firstMap_plus, Category.assoc, beta_plus]
      exact (chart P a A E (underToLaurent R) (laurentPlus_projection P a)).symm

/-- The positive geometric branch keeps the same full Laurent square. -/
theorem second_beta : second P a A E ≫ beta P a (A ≫ E) =
    secondMap P a E ≫ onReference A (reference P a E) := by
  apply (DoubleCylinder.simplicial_isPushout (𝟙 _) (FourEdgeTree.firstOne E J)).hom_ext
  · simp only [← Category.assoc]
    change (_ ≫ second P a A E) ≫ _ = (_ ≫ secondMap P a E) ≫ _
    rw [second_cylinder, secondMap_edge, Category.assoc, beta_edge01]
    exact (edge P a A E 0 1).symm
  · apply coprod.hom_ext
    · simp only [← Category.assoc]
      change (FourEdgeTree.secondZero E J ≫ second P a A E) ≫ _ =
        (FourEdgeTree.secondZero E J ≫ secondMap P a E) ≫ _
      rw [second_zero, secondMap_zero, Category.assoc, beta_zero]
      exact (vertex P a A E 0).symm
    · simp only [← Category.assoc]
      change (FourEdgeTree.firstInSecond E J ≫ second P a A E) ≫ _ =
        (FourEdgeTree.firstInSecond E J ≫ secondMap P a E) ≫ _
      rw [second_first, secondMap_first, first_beta]

/-- The inverse geometric branch retains its own original edge. -/
theorem third_beta : third P a A E ≫ beta P a (A ≫ E) =
    thirdMap P a E ≫ onReference A (reference P a E) := by
  apply (DoubleCylinder.simplicial_isPushout (FourEdgeTree.secondZero E J) (𝟙 _)).hom_ext
  · simp only [← Category.assoc]
    change (_ ≫ third P a A E) ≫ _ = (_ ≫ thirdMap P a E) ≫ _
    rw [third_cylinder, thirdMap_edge, Category.assoc, beta_edge03]
    exact (edge P a A E 0 3).symm
  · apply coprod.hom_ext
    · simp only [← Category.assoc]
      change (FourEdgeTree.secondInThird E J ≫ third P a A E) ≫ _ =
        (FourEdgeTree.secondInThird E J ≫ thirdMap P a E) ≫ _
      rw [third_second, thirdMap_second, second_beta]
    · simp only [← Category.assoc]
      change (FourEdgeTree.thirdThree E J ≫ third P a A E) ≫ _ =
        (FourEdgeTree.thirdThree E J ≫ thirdMap P a E) ≫ _
      rw [third_three, thirdMap_three, Category.assoc, beta_three]
      exact (vertex P a A E 3).symm

/-- The entire four-cylinder attachment commutes in the full Laurent nerve before realization. -/
theorem beta_naturality : map P a A E ≫ beta P a (A ≫ E) =
    beta P a E ≫ onReference A (reference P a E) := by
  apply (DoubleCylinder.simplicial_isPushout
    (FourEdgeTree.thirdThree E J) (FourEdgeTree.attachment E J)).hom_ext
  · simp only [← Category.assoc]
    change (FourEdgeTree.edge34 E J ≫ map P a A E) ≫ _ =
      (FourEdgeTree.edge34 E J ≫ beta P a E) ≫ _
    rw [map_edge34, beta_edge34, Category.assoc, beta_edge34]
    exact (edge P a A E 3 4).symm
  · apply coprod.hom_ext
    · simp only [← Category.assoc]
      change (FourEdgeTree.thirdInTree E J ≫ map P a A E) ≫ _ =
        (FourEdgeTree.thirdInTree E J ≫ beta P a E) ≫ _
      rw [map_third, beta_third, third_beta]
    · simp only [← Category.assoc]
      change (FourEdgeTree.minusVertex E J ≫ map P a A E) ≫ _ =
        (FourEdgeTree.minusVertex E J ≫ beta P a E) ≫ _
      rw [map_minus, beta_minus, Category.assoc, beta_minus]
      exact (chart P a A E (underToLaurentInvert R) (laurentMinus_projection P a)).symm

end Quillen.PerfectComplexes.BassProjectionPath.WholeReference.FourEdge.Precomp
