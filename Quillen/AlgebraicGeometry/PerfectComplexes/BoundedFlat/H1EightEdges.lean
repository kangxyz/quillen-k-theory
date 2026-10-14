/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.H1WholeNative
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.H1MergedOldNative

/-! Eight complete scalar cube edges shared by the five original faces now in one actual family. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity
open Quillen.PolynomialBaseChange Quillen.Scheme.CoefficientBaseChange
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassH1Merged

/-- The whole original H0/positive-chart edge survives in the joint scalar family. -/
theorem h0_plus_scalar (s : unitInterval) :
    BassH1Order.h0Parameter (s, 0) = BassH1Order.plusParameter (0, s) :=
  congrArg (StdSimplex.map BassH1Order.oldIndex) (BassH0Merged.h0_plus_scalar s)

/-- The separate original inverse chart edge survives with its literal scalar values. -/
theorem h0_minus_scalar (s : unitInterval) :
    BassH1Order.h0Parameter (s, 1) = BassH1Order.minusParameter (0, s) :=
  congrArg (StdSimplex.map BassH1Order.oldIndex) (BassH0Merged.h0_minus_scalar s)

/-- The entire source H0/bottom edge is retained without reparameterization. -/
theorem h0_bottom_scalar (t : unitInterval) :
    BassH1Order.h0Parameter (0, t) = BassH1Order.bottomParameter.{u} (0, t) :=
  congrArg (StdSimplex.map BassH1Order.oldIndex) (BassH0Merged.h0_bottom_scalar.{u} t)

/-- The old positive chart/bottom edge remains literally shared. -/
theorem plus_bottom_scalar (r : unitInterval) :
    BassH1Order.plusParameter (r, 0) = BassH1Order.bottomParameter.{u} (r, 0) :=
  congrArg (StdSimplex.map BassH1Order.oldIndex) (BassH0Merged.plus_bottom_scalar.{u} r)

/-- The old inverse chart/bottom edge retains the distinct negative cylinder endpoint. -/
theorem minus_bottom_scalar (r : unitInterval) :
    BassH1Order.minusParameter (r, 0) = BassH1Order.bottomParameter.{u} (r, 1) :=
  congrArg (StdSimplex.map BassH1Order.oldIndex) (BassH0Merged.minus_bottom_scalar.{u} r)

/-- The whole original H1/positive-chart edge, for every original composition parameter. -/
theorem h1_plus_scalar (s : unitInterval) :
    BassH1Order.h1Parameter.{u} (s, 0) = BassH1Order.plusParameter (1, s) :=
  BassH1Order.h1_plus_scalar s

/-- The original inverse H1/chart edge, including the shared half-time point. -/
theorem h1_minus_scalar (s : unitInterval) :
    BassH1Order.h1Parameter.{u} (s, 1) = BassH1Order.minusParameter (1, s) :=
  BassH1Order.h1_minus_scalar s

/-- The whole original H1/bottom target edge, with the cylinder parameter unchanged. -/
theorem h1_bottom_scalar (t : unitInterval) :
    BassH1Order.h1Parameter.{u} (0, t) = BassH1Order.bottomParameter.{u} (1, t) :=
  BassH1Order.h1_bottom_scalar t

variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- H1's entire target edge retains M's exact original endpoint, without supplying a whole M. -/
theorem h1_top_native (n : ℕ) (t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P u v) n (BassH1Order.h1Parameter.{u} (1, t), x) =
    ((boundedFlatCoefficientPolynomialSpanCompositionHomotopy P u v).postcomp
      (boundedFlatCoefficientBassSquareComparison P c)).level n
      (1, HomotopyPushout.cylinder
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)) n (t, x)) :=
  (h1_native P u v n 1 t x).trans
    (((boundedFlatCoefficientBassCompositeComparison P u v).at_one n _).trans
      (((boundedFlatCoefficientPolynomialSpanCompositionHomotopy P u v).postcomp
        (boundedFlatCoefficientBassSquareComparison P c)).at_one n _).symm)

end Quillen.PerfectComplexes.BassH1Merged
