/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassH0MergedFaces
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassH0TopNativeEdge

/-! Whole original H0, fixed chart, and bottom values in one actual supported reference family. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity
open Quillen.PolynomialBaseChange Quillen.Scheme.CoefficientBaseChange
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters Quillen.LoopPrespectrum
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassH0Merged
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- Every actual positive chart value is retained through its original supported triple face. -/
theorem plus_native (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P u v) n (BassSupportOrder.plusParameter (r, s), x) =
      (boundedFlatCoefficientBassCompositionPlusChart P u v).level n
        (r, (s, (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)).map n x)) := by
  calc
    _ = prespectrumSimplexFamily (BassReferenceMerge.simplex P u v) n
        (BassReferenceMerge.plusParameter (r, s), x) := by
      obtain ⟨i, y, hy⟩ := BassPrimitiveSupport.plus_chart_support (r, s)
      change prespectrumSimplexFamily (simplex P u v) n
        (StdSimplex.map BassSupportOrder.oldIndex (BassReferenceMerge.plusParameter (r, s)), x) = _
      rw [← hy]
      have hm : Monotone (BassSupportOrder.oldIndex ∘
          ((BassPrimitiveSupport.rectangleFace i ≫ BassOverlap.plusFace) ≫
            BassReferenceMerge.chartFace).toOrderHom) := by
        simpa only [Category.assoc] using BassSupportOrder.oldPlus_monotone i
      exact old_family_face P u v _ hm n y x
    _ = _ := BassReferenceMerge.plus_native P u v n r s x

/-- Every actual inverse chart value is retained, including its distinct original chart maps. -/
theorem minus_native (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P u v) n (BassSupportOrder.minusParameter (r, s), x) =
      (boundedFlatCoefficientBassCompositionMinusChart P u v).level n
        (r, (s, (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)).map n x)) := by
  calc
    _ = prespectrumSimplexFamily (BassReferenceMerge.simplex P u v) n
        (BassReferenceMerge.minusParameter (r, s), x) := by
      obtain ⟨i, y, hy⟩ := BassPrimitiveSupport.minus_chart_support (r, s)
      change prespectrumSimplexFamily (simplex P u v) n
        (StdSimplex.map BassSupportOrder.oldIndex (BassReferenceMerge.minusParameter (r, s)), x) = _
      rw [← hy]
      have hm : Monotone (BassSupportOrder.oldIndex ∘
          ((BassPrimitiveSupport.rectangleFace i ≫ BassOverlap.minusFace) ≫
            BassReferenceMerge.chartFace).toOrderHom) := by
        simpa only [Category.assoc] using BassSupportOrder.oldMinus_monotone i
      exact old_family_face P u v _ hm n y x
    _ = _ := BassReferenceMerge.minus_native P u v n r s x

/-- The whole prescribed original bottom remains the actual independently varying product family. -/
theorem bottom_native (n : ℕ) (r t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P u v) n (BassSupportOrder.bottomParameter.{u} (r, t), x) =
      (Homotopy.precomp (boundedFlatCoefficientBassSquareComparison P a)
        (boundedFlatCoefficientLaurentCompositionHomotopy P u v)).level n
        (r, HomotopyPushout.cylinder
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)) n (t, x)) := by
  change prespectrumSimplexFamily (simplex P u v) n
    (StdSimplex.map BassSupportOrder.oldIndex
      (StdSimplex.map BassReferenceMerge.bottomFace.toOrderHom
        (BassLaurentBottomFace.parameter (r, t))), x) = _
  rw [old_family_face P u v BassReferenceMerge.bottomFace BassSupportOrder.bottom_monotone]
  exact BassReferenceMerge.bottom_native P u v n r t x

/-- Original H0 values retain their exact pasted parameters via the six actual triple supports. -/
theorem h0_family (n : ℕ) (z : unitInterval × unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P u v) n (BassSupportOrder.h0Parameter z, x) =
      prespectrumSimplexFamily (BassH0Merge.simplex P u v) n (BassH0Diagram.parameter z, x) := by
  change prespectrumSimplexFamily (simplex P u v) n
    (StdSimplex.map BassSupportOrder.h0Index (BassH0Diagram.parameter z), x) = _
  obtain ⟨α, hα, i, y, hy⟩ := BassPrimitiveSupport.h0_support z
  rw [← hy]
  rcases Set.mem_insert_iff.mp hα with hα | hα
  · subst α
    exact h0_family_face P u v _ (BassSupportOrder.h0Plus_monotone i) n y x
  · have hα' := Set.mem_singleton_iff.mp hα
    subst α
    exact h0_family_face P u v _ (BassSupportOrder.h0Minus_monotone i) n y x

/-- The complete original H0 cylinder face is now evaluated in the same actual common simplex. -/
theorem h0_native (n : ℕ) (s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P u v) n (BassSupportOrder.h0Parameter (s, t), x) =
      (boundedFlatCoefficientBassComparisonHomotopy P (u ≫ v)).level n
        (s, HomotopyPushout.cylinder
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)) n (t, x)) := by
  rw [h0_family, BassH0Merge.simplex_original]
  exact BassH0Diagram.composition_H0 P u v n s t x

/-- The fourth H0 edge retains M's original native endpoint before constructing its whole family. -/
theorem h0_top_native (n : ℕ) (t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P u v) n (BassSupportOrder.h0Parameter (1, t), x) =
      ((boundedFlatCoefficientPolynomialSpanCompositionHomotopy P u v).postcomp
        (boundedFlatCoefficientBassSquareComparison P c)).level n
          (0, HomotopyPushout.cylinder
            (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
            (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)) n (t, x)) :=
  (h0_family P u v n (1, t) x).trans (BassH0Merge.top_native_edge P u v n t x)

/-- The genuine common family fixes the original basepoint at every scalar parameter. -/
theorem family_point (n : ℕ) (z : StdSimplex ℝ (Fin 63)) :
    prespectrumSimplexFamily (simplex P u v) n
      (z, (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).point n) =
      (originalPrespectrum (boundedFlatPerfectWaldhausen
        (space (op P, (laurentUnderFunctor R).obj c)))).point n :=
  prespectrumSimplexFamily_point (simplex P u v) n z

/-- The independent native structure time remains separate from every scalar face parameter. -/
theorem family_structure (n : ℕ) (z : StdSimplex ℝ (Fin 63))
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n)
    (t : unitInterval) :
    prespectrumSimplexFamily (simplex P u v) (n + 1)
      (z, (originalPrespectrum
        (boundedFlatPerfectWaldhausen (space (op P, a)))).structureMap n x t) =
    (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (laurentUnderFunctor R).obj c)))).structureMap n
        (prespectrumSimplexFamily (simplex P u v) n (z, x)) t :=
  prespectrumSimplexFamily_structure (simplex P u v) n z x t

end Quillen.PerfectComplexes.BassH0Merged
