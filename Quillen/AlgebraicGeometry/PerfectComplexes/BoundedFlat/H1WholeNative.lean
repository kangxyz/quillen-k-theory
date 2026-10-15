/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Aglib.Algebra.Polynomial.Laurent.UnderSquare
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.H1ContinuousParameter
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.H1MergedComponentNative

/-! The whole prescribed native H1 family in the actual common 130-simplex. -/
@[expose] public section

open CommRingCat.PolynomialLaurent

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum Quillen.NativePathCells
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassH1Merged
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- Every parameter pair and every level, including zero, has the exact original native H1 value. -/
theorem h1_native (n : ℕ) (s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P u v) n (BassH1Order.h1Parameter.{u} (s, t), x) =
    (boundedFlatCoefficientBassCompositeComparison P u v).level n
      (s, HomotopyPushout.cylinder
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)) n (t, x)) := by
  rcases cover s with ⟨r, rfl⟩ | ⟨r, rfl⟩
  · rw [BassH1Order.h1_lower]
    exact first_cell_native P u v n r t x
  · rcases three_cover t with ⟨q, rfl⟩ | ⟨q, rfl⟩ | ⟨q, rfl⟩
    · rw [BassH1Order.h1_plus_cell]
      exact plus_cell_native P u v n r q x
    · rw [BassH1Order.h1_middle_cell]
      exact middle_cell_native P u v n r q x
    · rw [BassH1Order.h1_minus_cell]
      exact minus_cell_native P u v n r q x

/-- The entire H1 parameter family fixes the original levelwise basepoint. -/
theorem h1_point (n : ℕ) (s t : unitInterval) :
    prespectrumSimplexFamily (simplex P u v) n
      (BassH1Order.h1Parameter.{u} (s, t),
        (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).point n) =
    (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (laurentUnderFunctor R).obj c)))).point n :=
  family_point P u v n _

/-- Original structure time z remains independent of both H1 parameters s and t. -/
theorem h1_structure (n : ℕ) (s t z : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P u v) (n + 1)
      (BassH1Order.h1Parameter.{u} (s, t),
        (originalPrespectrum (boundedFlatPerfectWaldhausen
          (space (op P, a)))).structureMap n x z) =
    (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (laurentUnderFunctor R).obj c)))).structureMap n
        (prespectrumSimplexFamily (simplex P u v) n
          (BassH1Order.h1Parameter.{u} (s, t), x)) z :=
  family_structure P u v n _ x z

end Quillen.PerfectComplexes.BassH1Merged
