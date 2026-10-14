/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.H1MergedFaces
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.H1ReindexedParameters

/-! Whole original H1 component values in the actual common 130-simplex, at every level. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity
open Quillen.PolynomialBaseChange Quillen.Scheme.CoefficientBaseChange
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters Quillen.LoopPrespectrum
open Quillen.NativePathCells
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassH1Merged
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- All actual first-component points retain their original H0 scalar values. -/
theorem first_family (n : ℕ) (s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P u v) n (BassH1Order.firstParameter (s, t), x) =
    prespectrumSimplexFamily (BassH1Components.firstSimplex P u v) n
      (BassH0Diagram.parameter (s, t), x) := by
  change prespectrumSimplexFamily (simplex P u v) n
    (StdSimplex.map BassH1Order.firstIndex (BassH0Diagram.parameter (s, t)), x) = _
  obtain ⟨α, hα, i, y, hy⟩ := BassPrimitiveSupport.h0_support (s, t)
  rw [← hy]
  rcases Set.mem_insert_iff.mp hα with hα | hα
  · subst α
    exact first_family_face P u v _ (BassH1Order.firstPlus_monotone i) n y x
  · have hα' := Set.mem_singleton_iff.mp hα
    subst α
    exact first_family_face P u v _ (BassH1Order.firstMinus_monotone i) n y x

/-- All actual middle-component points retain their original H0 scalar values. -/
theorem middle_family (n : ℕ) (s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P u v) n (BassH1Order.middleParameter (s, t), x) =
    prespectrumSimplexFamily (BassH1Components.middleSimplex P u v) n
      (BassH0Diagram.parameter (s, t), x) := by
  change prespectrumSimplexFamily (simplex P u v) n
    (StdSimplex.map BassH1Order.middleIndex (BassH0Diagram.parameter (s, t)), x) = _
  obtain ⟨α, hα, i, y, hy⟩ := BassPrimitiveSupport.h0_support (s, t)
  rw [← hy]
  rcases Set.mem_insert_iff.mp hα with hα | hα
  · subst α
    exact middle_family_face P u v _ (BassH1Order.middlePlus_monotone i) n y x
  · have hα' := Set.mem_singleton_iff.mp hα
    subst α
    exact middle_family_face P u v _ (BassH1Order.middleMinus_monotone i) n y x

/-- The entire actual plus varying-family product is retained through its proved small supports. -/
theorem plus_product_family (n : ℕ) (s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P u v) n
      (BassH1Order.plusProductParameter.{u} (s, t), x) =
    prespectrumSimplexFamily (BassH1Components.chartProduct P u v (underToLaurent R)) n
      (BassH1Components.plusParameter.{u} (s, t), x) := by
  change prespectrumSimplexFamily (simplex P u v) n
    (StdSimplex.map BassH1Order.plusProductIndex
      (BassH1Components.plusParameter.{u} (s, t)), x) = _
  obtain ⟨i, j, z, hz⟩ := BassH1Support.plus_support.{u} s t
  rw [← hz]
  exact plus_family_face P u v _ (BassH1Order.plusProduct_monotone i j) n z x

/-- The entire actual minus varying-family product is retained through its proved small supports. -/
theorem minus_product_family (n : ℕ) (s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P u v) n
      (BassH1Order.minusProductParameter.{u} (s, t), x) =
    prespectrumSimplexFamily (BassH1Components.chartProduct P u v (underToLaurentInvert R)) n
      (BassH1Components.minusParameter.{u} (s, t), x) := by
  change prespectrumSimplexFamily (simplex P u v) n
    (StdSimplex.map BassH1Order.minusProductIndex
      (BassH1Components.minusParameter.{u} (s, t)), x) = _
  obtain ⟨i, j, z, hz⟩ := BassH1Support.minus_support.{u} s t
  rw [← hz]
  exact minus_family_face P u v _ (BassH1Order.minusProduct_monotone i j) n z x

/-- Exact original H1 values on the complete first cell, including level zero and every input. -/
theorem first_cell_native (n : ℕ) (s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P u v) n (BassH1Order.firstParameter (s, t), x) =
    (boundedFlatCoefficientBassCompositeComparison P u v).level n
      (lower s, HomotopyPushout.cylinder
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)) n (t, x)) :=
  (first_family P u v n s t x).trans (BassH1NativeCells.first_native P u v n s t x)

/-- Exact original H1 values on the complete plus cell, including level zero and every input. -/
theorem plus_cell_native (n : ℕ) (s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P u v) n (BassH1Order.plusProductParameter.{u} (s, t), x) =
    (boundedFlatCoefficientBassCompositeComparison P u v).level n
      (upper s, HomotopyPushout.cylinder
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)) n (lower t, x)) :=
  (plus_product_family P u v n s t x).trans (BassH1NativeCells.plus_native P u v n s t x)

/-- Exact original H1 values on the complete middle cell, including level zero and every input. -/
theorem middle_cell_native (n : ℕ) (s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P u v) n (BassH1Order.middleParameter (s, t), x) =
    (boundedFlatCoefficientBassCompositeComparison P u v).level n
      (upper s, HomotopyPushout.cylinder
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)) n (upper (lower t), x)) :=
  (middle_family P u v n s t x).trans (BassH1NativeCells.middle_native P u v n s t x)

/-- Exact original H1 values on the complete minus cell, including level zero and every input. -/
theorem minus_cell_native (n : ℕ) (s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P u v) n (BassH1Order.minusProductParameter.{u} (s, t), x) =
    (boundedFlatCoefficientBassCompositeComparison P u v).level n
      (upper s, HomotopyPushout.cylinder
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)) n (upper (upper t), x)) :=
  (minus_product_family P u v n s t x).trans (BassH1NativeCells.minus_native P u v n s t x)

/-- Every common scalar value fixes the original prespectrum basepoint. -/
theorem family_point (n : ℕ) (z : StdSimplex ℝ (Fin 131)) :
    prespectrumSimplexFamily (simplex P u v) n
      (z, (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).point n) =
    (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (laurentUnderFunctor R).obj c)))).point n :=
  prespectrumSimplexFamily_point (simplex P u v) n z

/-- Structure time remains independent of every scalar component parameter. -/
theorem family_structure (n : ℕ) (z : StdSimplex ℝ (Fin 131))
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n)
    (t : unitInterval) :
    prespectrumSimplexFamily (simplex P u v) (n + 1)
      (z, (originalPrespectrum
        (boundedFlatPerfectWaldhausen (space (op P, a)))).structureMap n x t) =
    (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (laurentUnderFunctor R).obj c)))).structureMap n
        (prespectrumSimplexFamily (simplex P u v) n (z, x)) t :=
  prespectrumSimplexFamily_structure (simplex P u v) n z x t

end Quillen.PerfectComplexes.BassH1Merged
