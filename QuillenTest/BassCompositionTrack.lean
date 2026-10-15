/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CompositionTrack
public import Aglib.AlgebraicGeometry.AffineSpace.PolynomialLaurent.Basic

/-! The actual positive and inverse-coordinate Laurent legs retain their original binary tracks. -/
@[expose] public section

open AlgebraicGeometry.Scheme.PolynomialLaurent
open Quillen.PerfectComplexes

noncomputable section
open CategoryTheory AlgebraicGeometry
  AlgebraicGeometry.Scheme.PolynomialLaurent
universe u
namespace QuillenTest.BassCompositionTrack

open Quillen

/-- The positive Laurent face is the actual existing two-part geometric composition homotopy. -/
theorem plus_original_final_face (R : CommRingCat.{u}) :
    (boundedFlatNormalizedCompTrackComparison (laurentPlus R)
      (polynomialProjection R)).at 1 =
        boundedFlatPerfectPrespectrumCompHomotopy (laurentPlus R) (polynomialProjection R) :=
  Quillen.LoopPrespectrum.Homotopy.RelHomotopy.at_one _

/-- The inverse-coordinate Laurent face retains its separate original two-part track. -/
theorem minus_original_final_face (R : CommRingCat.{u}) :
    (boundedFlatNormalizedCompTrackComparison (laurentMinus R)
      (polynomialProjection R)).at 1 =
        boundedFlatPerfectPrespectrumCompHomotopy (laurentMinus R) (polynomialProjection R) :=
  Quillen.LoopPrespectrum.Homotopy.RelHomotopy.at_one _

/-- The initial face is the actual total comparison, not a newly chosen homotopy. -/
theorem plus_original_initial_face (R : CommRingCat.{u}) :
    (boundedFlatNormalizedCompTrackComparison (laurentPlus R)
      (polynomialProjection R)).at 0 =
        boundedFlatNormalizedCompTrack (laurentPlus R) (polynomialProjection R) :=
  Quillen.LoopPrespectrum.Homotopy.RelHomotopy.at_zero _

end QuillenTest.BassCompositionTrack
