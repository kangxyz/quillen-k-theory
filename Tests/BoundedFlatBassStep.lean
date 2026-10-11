/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.BoundedFlatBassStep

/-! Original scalar, nullhomotopy and loop coordinates in the actual bounded-flat Bass step. -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.PerfectComplexes Quillen.LoopPrespectrum
open Quillen.Scheme.PolynomialLaurent Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.Tests.BoundedFlatBassStep

/-- The actual source leg becomes the literal positive Laurent composite. -/
theorem source_comparison (R : CommRingCat.{u}) :
    boundedFlatBassSourceLeg R ≫ boundedFlatBassSquareComparison R =
      boundedFlatPerfectPrespectrumMap (polynomialProjection R) ≫
        boundedFlatPerfectPrespectrumMap (laurentPlus R) :=
  boundedFlatBassSourceLeg_comparison R

/-- The inverse acting on every original term is the inverse Laurent scalar. -/
theorem inverse_terms (R : CommRingCat.{u})
    (K : BoundedFlatPerfect (Spec (.of (LaurentPolynomial R)))) (n : ℤ) :
    ((boundedFlatPerfect _).ι.map
      ((boundedFlatPerfectGlobalUnitIso _ (laurentGlobalUnit R)).inv.app K)).f n =
      (SchemeSheaf.globalScalar _ (↑(laurentGlobalUnit R)⁻¹)).app (K.obj.X n) :=
  boundedFlatPerfectGlobalUnitIso_inv_terms _ _ K n

/-- The complete transition loop retains the actual conjugated Laurent-unit track. -/
theorem whole_transition (R : CommRingCat.{u}) (n : ℕ)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (Spec R))).space n)
    (s : unitInterval) :
    Path.toContinuousMap ((boundedFlatAffineBassTransition R).map n x) s =
      (((boundedFlatLaurentUnitHomotopy R).postcomp
        (mappingConeInclusion (boundedFlatBassSquareComparison R))).conjugateToZero
          (boundedFlatBassLaurentNullHomotopy R)).level n (s, x) :=
  boundedFlatAffineBassTransition_apply R n x s

/-- The unit's path coordinate remains independent from the prespectrum structure coordinate. -/
theorem unit_structure (R : CommRingCat.{u}) (n : ℕ) (s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (Spec R))).space n) :
    (boundedFlatLaurentUnitHomotopy R).level (n + 1)
      (s, (originalPrespectrum (boundedFlatPerfectWaldhausen (Spec R))).structureMap n x t) =
      (originalPrespectrum (boundedFlatPerfectWaldhausen
        (Spec (.of (LaurentPolynomial R))))).structureMap n
          ((boundedFlatLaurentUnitHomotopy R).level n (s, x)) t :=
  (boundedFlatLaurentUnitHomotopy R).comm n s x t

/-- The original nullhomotopy ends at the genuine cone basepoint. -/
theorem null_endpoint (R : CommRingCat.{u}) (n : ℕ)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (Spec R))).space n) :
    (boundedFlatBassLaurentNullHomotopy R).level n (1, x) =
      (mappingCone (boundedFlatBassSquareComparison R)).point n :=
  (boundedFlatBassLaurentNullHomotopy R).at_one n x

end Quillen.Tests.BoundedFlatBassStep
