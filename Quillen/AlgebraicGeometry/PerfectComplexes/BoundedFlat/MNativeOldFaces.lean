/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MNativePasting

/-! All five unchanged original faces in the common native family under its actual support data. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity
open Quillen.PolynomialBaseChange AlgebraicGeometry.Scheme.CoefficientBaseChange
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassMFamilyTransfer
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c) {k : ℕ}
  (N : Fin (k + 1) → BassOverlap.Node P u v)
  (f : Fin 45 → Fin (k + 1)) (g : Fin 131 → Fin (k + 1))
  (hn : ∀ i, N (g i) = BassH1Merged.nodes P u v i) (o : SupportOrders f g)

include hn o in
/-- Every value of the original plus face is retained, with its native inputs and times. -/
theorem plus_native (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (nativeSimplex P u v N) n (BassMScalarPasting.plus g (r, s), x) =
    (boundedFlatCoefficientBassCompositionPlusChart P u v).level n
      (r, (s, (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)).map n x)) :=
  (old_plus_value P u v N f g hn o n r s x).trans
    (BassH1Merged.plus_native P u v n r s x)

include hn o in
/-- Every value of the original minus face is retained, with its native inputs and times. -/
theorem minus_native (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (nativeSimplex P u v N) n (BassMScalarPasting.minus g (r, s), x) =
    (boundedFlatCoefficientBassCompositionMinusChart P u v).level n
      (r, (s, (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)).map n x)) :=
  (old_minus_value P u v N f g hn o n r s x).trans
    (BassH1Merged.minus_native P u v n r s x)

include hn o in
/-- Every value of the original bottom face is retained, with its native inputs and times. -/
theorem bottom_native (n : ℕ) (r t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (nativeSimplex P u v N) n (BassMScalarPasting.bottom.{u} g (r, t), x) =
    (Homotopy.precomp (boundedFlatCoefficientBassSquareComparison P a)
      (boundedFlatCoefficientLaurentCompositionHomotopy P u v)).level n
      (r, HomotopyPushout.cylinder
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)) n (t, x)) :=
  (old_bottom_value P u v N f g hn o n r t x).trans
    (BassH1Merged.bottom_native P u v n r t x)

include hn o in
/-- Every value of the original h0 face is retained, with its native inputs and times. -/
theorem h0_native (n : ℕ) (s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (nativeSimplex P u v N) n (BassMScalarPasting.h0 g (s, t), x) =
    (boundedFlatCoefficientBassComparisonHomotopy P (u ≫ v)).level n
      (s, HomotopyPushout.cylinder
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)) n (t, x)) :=
  (old_h0_value P u v N f g hn o n s t x).trans
    (BassH1Merged.h0_native P u v n s t x)

include hn o in
/-- Every value of the original h1 face is retained, with its native inputs and times. -/
theorem h1_native (n : ℕ) (s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (nativeSimplex P u v N) n (BassMScalarPasting.h1.{u} g (s, t), x) =
    (boundedFlatCoefficientBassCompositeComparison P u v).level n
      (s, HomotopyPushout.cylinder
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)) n (t, x)) :=
  (old_h1_value P u v N f g hn o n s t x).trans
    (BassH1Merged.h1_native P u v n s t x)

end Quillen.PerfectComplexes.BassMFamilyTransfer
