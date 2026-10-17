/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassProjectionFourEdgeReanchorMap

/-! Full Laurent-reference naturality of the entire original four-edge attachment. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
open MonoidalCategory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassProjectionPath.WholeReference.FourEdge.Reanchor
open BassH0Merge CommonReferenceNerve CommonReferenceNerve.CutOpenCarrier
variable {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R)
variable {V : Model.{u + 1}}
  (E E' : V ⟶ modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))
  (δ : E'.functor ≅ E.functor)
local notation "J" => normalizedMap (polynomialProjection P a)

/-- The first complete pushout obeys the original Laurent reference square. -/
theorem first_beta : first P a E E' δ ≫ beta P a E' =
    firstMap P a E ≫ onReference (isoWhiskerRight δ (BassProjectionPath.source P a).functor) := by
  apply (DoubleCylinder.simplicial_isPushout (𝟙 _) (FourEdgeTree.attachment E J)).hom_ext
  · simp only [← Category.assoc]
    change (_ ≫ first P a E E' δ) ≫ _ = (_ ≫ firstMap P a E) ≫ _
    rw [first_cylinder, firstMap_edge, Category.assoc, beta_edge12]
    exact (edge P a E E' δ 1 2).symm
  · apply coprod.hom_ext
    · simp only [← Category.assoc]
      change (FourEdgeTree.firstOne E J ≫ first P a E E' δ) ≫ _ =
        (FourEdgeTree.firstOne E J ≫ firstMap P a E) ≫ _
      rw [first_one, firstMap_one, Category.assoc, beta_one]
      exact (vertex P a E E' δ 1).symm
    · simp only [← Category.assoc]
      change (FourEdgeTree.firstPlus E J ≫ first P a E E' δ) ≫ _ =
        (FourEdgeTree.firstPlus E J ≫ firstMap P a E) ≫ _
      rw [first_plus, firstMap_plus, Category.assoc, beta_plus]
      exact (chart P a E E' δ (underToLaurent R) (laurentPlus_projection P a)).symm

/-- The positive geometric branch keeps the same full Laurent square. -/
theorem second_beta : second P a E E' δ ≫ beta P a E' =
    secondMap P a E ≫ onReference (isoWhiskerRight δ (BassProjectionPath.source P a).functor) := by
  apply (DoubleCylinder.simplicial_isPushout (𝟙 _) (FourEdgeTree.firstOne E J)).hom_ext
  · simp only [← Category.assoc]
    change (_ ≫ second P a E E' δ) ≫ _ = (_ ≫ secondMap P a E) ≫ _
    rw [second_cylinder, secondMap_edge, Category.assoc, beta_edge01]
    exact (edge P a E E' δ 0 1).symm
  · apply coprod.hom_ext
    · simp only [← Category.assoc]
      change (FourEdgeTree.secondZero E J ≫ second P a E E' δ) ≫ _ =
        (FourEdgeTree.secondZero E J ≫ secondMap P a E) ≫ _
      rw [second_zero, secondMap_zero, Category.assoc, beta_zero]
      exact (vertex P a E E' δ 0).symm
    · simp only [← Category.assoc]
      change (FourEdgeTree.firstInSecond E J ≫ second P a E E' δ) ≫ _ =
        (FourEdgeTree.firstInSecond E J ≫ secondMap P a E) ≫ _
      rw [second_first, secondMap_first, first_beta]

/-- The inverse geometric branch retains its own original edge. -/
theorem third_beta : third P a E E' δ ≫ beta P a E' =
    thirdMap P a E ≫ onReference (isoWhiskerRight δ (BassProjectionPath.source P a).functor) := by
  apply (DoubleCylinder.simplicial_isPushout (FourEdgeTree.secondZero E J) (𝟙 _)).hom_ext
  · simp only [← Category.assoc]
    change (_ ≫ third P a E E' δ) ≫ _ = (_ ≫ thirdMap P a E) ≫ _
    rw [third_cylinder, thirdMap_edge, Category.assoc, beta_edge03]
    exact (edge P a E E' δ 0 3).symm
  · apply coprod.hom_ext
    · simp only [← Category.assoc]
      change (FourEdgeTree.secondInThird E J ≫ third P a E E' δ) ≫ _ =
        (FourEdgeTree.secondInThird E J ≫ thirdMap P a E) ≫ _
      rw [third_second, thirdMap_second, second_beta]
    · simp only [← Category.assoc]
      change (FourEdgeTree.thirdThree E J ≫ third P a E E' δ) ≫ _ =
        (FourEdgeTree.thirdThree E J ≫ thirdMap P a E) ≫ _
      rw [third_three, thirdMap_three, Category.assoc, beta_three]
      exact (vertex P a E E' δ 3).symm

/-- The entire four-cylinder attachment commutes in the full Laurent nerve before realization. -/
theorem beta_naturality : map P a E E' δ ≫ beta P a E' =
    beta P a E ≫ onReference (isoWhiskerRight δ (BassProjectionPath.source P a).functor) := by
  apply (DoubleCylinder.simplicial_isPushout
    (FourEdgeTree.thirdThree E J) (FourEdgeTree.attachment E J)).hom_ext
  · simp only [← Category.assoc]
    change (FourEdgeTree.edge34 E J ≫ map P a E E' δ) ≫ _ =
      (FourEdgeTree.edge34 E J ≫ beta P a E) ≫ _
    rw [map_edge34, beta_edge34, Category.assoc, beta_edge34]
    exact (edge P a E E' δ 3 4).symm
  · apply coprod.hom_ext
    · simp only [← Category.assoc]
      change (FourEdgeTree.thirdInTree E J ≫ map P a E E' δ) ≫ _ =
        (FourEdgeTree.thirdInTree E J ≫ beta P a E) ≫ _
      rw [map_third, beta_third, third_beta]
    · simp only [← Category.assoc]
      change (FourEdgeTree.minusVertex E J ≫ map P a E E' δ) ≫ _ =
        (FourEdgeTree.minusVertex E J ≫ beta P a E) ≫ _
      rw [map_minus, beta_minus, Category.assoc, beta_minus]
      exact (chart P a E E' δ (underToLaurentInvert R) (laurentMinus_projection P a)).symm

end Quillen.PerfectComplexes.BassProjectionPath.WholeReference.FourEdge.Reanchor
