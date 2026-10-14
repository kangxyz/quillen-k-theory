/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.H1OldSupport

/-! The four whole fixed H0/chart/bottom faces remain unchanged in the common H1 family. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity
open Quillen.PolynomialBaseChange Quillen.Scheme.CoefficientBaseChange
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassH1Merged
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- Every original plus chart parameter retains its actual old62 family value. -/
theorem old_plus_family (n : ℕ) (s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P u v) n (BassH1Order.plusParameter (s, t), x) =
    prespectrumSimplexFamily (BassH0Merged.simplex P u v) n
      (BassSupportOrder.plusParameter (s, t), x) := by
  change prespectrumSimplexFamily (simplex P u v) n
    (StdSimplex.map BassH1Order.oldIndex (BassSupportOrder.plusParameter (s, t)), x) = _
  obtain ⟨i, y, hy⟩ := BassH1Support.old_plus_support (s, t)
  rw [← hy]
  exact old_family_face P u v _ (BassH1Order.oldPlus_monotone i) n y x

/-- Every original minus chart parameter retains its actual old62 family value. -/
theorem old_minus_family (n : ℕ) (s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P u v) n (BassH1Order.minusParameter (s, t), x) =
    prespectrumSimplexFamily (BassH0Merged.simplex P u v) n
      (BassSupportOrder.minusParameter (s, t), x) := by
  change prespectrumSimplexFamily (simplex P u v) n
    (StdSimplex.map BassH1Order.oldIndex (BassSupportOrder.minusParameter (s, t)), x) = _
  obtain ⟨i, y, hy⟩ := BassH1Support.old_minus_support (s, t)
  rw [← hy]
  exact old_family_face P u v _ (BassH1Order.oldMinus_monotone i) n y x

/-- The whole original bottom parameter retains its actual old62 independently varying value. -/
theorem old_bottom_family (n : ℕ) (s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P u v) n (BassH1Order.bottomParameter.{u} (s, t), x) =
    prespectrumSimplexFamily (BassH0Merged.simplex P u v) n
      (BassSupportOrder.bottomParameter.{u} (s, t), x) := by
  change prespectrumSimplexFamily (simplex P u v) n
    (StdSimplex.map BassH1Order.oldIndex (BassSupportOrder.bottomParameter.{u} (s, t)), x) = _
  obtain ⟨y, hy⟩ := BassH1Support.old_bottom_support.{u} (s, t)
  rw [← hy]
  exact old_family_face P u v _ BassH1Order.oldBottom_monotone n y x

/-- Every point of the complete original H0 keeps the exact old62 native pasting value. -/
theorem old_h0_family (n : ℕ) (s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P u v) n (BassH1Order.h0Parameter (s, t), x) =
    prespectrumSimplexFamily (BassH0Merged.simplex P u v) n
      (BassSupportOrder.h0Parameter (s, t), x) := by
  change prespectrumSimplexFamily (simplex P u v) n
    (StdSimplex.map BassH1Order.oldIndex (BassSupportOrder.h0Parameter (s, t)), x) = _
  rcases BassH1Support.old_h0_support (s, t) with ⟨i, y, hy⟩ | ⟨i, y, hy⟩
  · rw [← hy]
    exact old_family_face P u v _ (BassH1Order.oldH0Plus_monotone i) n y x
  · rw [← hy]
    exact old_family_face P u v _ (BassH1Order.oldH0Minus_monotone i) n y x

/-- The whole fixed original plus chart remains native at every parameter and prespectrum level. -/
theorem plus_native (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P u v) n (BassH1Order.plusParameter (r, s), x) =
    (boundedFlatCoefficientBassCompositionPlusChart P u v).level n
      (r, (s, (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)).map n x)) :=
  (old_plus_family P u v n r s x).trans (BassH0Merged.plus_native P u v n r s x)

/-- The whole fixed original minus chart remains native at every parameter and prespectrum level. -/
theorem minus_native (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P u v) n (BassH1Order.minusParameter (r, s), x) =
    (boundedFlatCoefficientBassCompositionMinusChart P u v).level n
      (r, (s, (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)).map n x)) :=
  (old_minus_family P u v n r s x).trans (BassH0Merged.minus_native P u v n r s x)

/-- The entire prescribed original bottom face uses its original Laurent composition homotopy. -/
theorem bottom_native (n : ℕ) (r t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P u v) n (BassH1Order.bottomParameter.{u} (r, t), x) =
    (Homotopy.precomp (boundedFlatCoefficientBassSquareComparison P a)
      (boundedFlatCoefficientLaurentCompositionHomotopy P u v)).level n
      (r, HomotopyPushout.cylinder
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)) n (t, x)) :=
  (old_bottom_family P u v n r t x).trans (BassH0Merged.bottom_native P u v n r t x)

/-- The whole prescribed H0 is unchanged in the same actual reference family as H1. -/
theorem h0_native (n : ℕ) (s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P u v) n (BassH1Order.h0Parameter (s, t), x) =
    (boundedFlatCoefficientBassComparisonHomotopy P (u ≫ v)).level n
      (s, HomotopyPushout.cylinder
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)) n (t, x)) :=
  (old_h0_family P u v n s t x).trans (BassH0Merged.h0_native P u v n s t x)

/-- The original H0 target still gives M's exact source endpoint before a whole M is constructed. -/
theorem h0_top_native (n : ℕ) (t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P u v) n (BassH1Order.h0Parameter (1, t), x) =
    ((boundedFlatCoefficientPolynomialSpanCompositionHomotopy P u v).postcomp
      (boundedFlatCoefficientBassSquareComparison P c)).level n
      (0, HomotopyPushout.cylinder
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)) n (t, x)) :=
  (old_h0_family P u v n 1 t x).trans (BassH0Merged.h0_top_native P u v n t x)

end Quillen.PerfectComplexes.BassH1Merged
