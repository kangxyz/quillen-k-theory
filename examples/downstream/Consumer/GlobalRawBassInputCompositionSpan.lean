/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalRawBassInputCompositionSpan

/-! Independent consumers of the original global positive chart-pair span composition. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
open Quillen.PerfectComplexes.GlobalRawBass
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u
namespace Consumer.GlobalRawBassInputCompositionSpan

/-- No geometric rectangle or higher filler is supplied by the downstream caller. -/
def positiveSpan (X : Scheme.{u}) :
    Homotopy (spanMap (laurentProjection.app X))
      (spanMap (projection.app X) ≫ spanMap (plus.app X)) :=
  InputCompositionSpan.positiveProjection X

/-- The actual endpoint is the composed original positive-span maps at every point. -/
theorem actual_target (X : Scheme.{u}) (n : ℕ) (x : (span X).space n) :
    (positiveSpan X).level n (1, x) =
      (spanMap (plus.app X)).map n ((spanMap (projection.app X)).map n x) :=
  (positiveSpan X).at_one n x

/-- The positive pilot retains an arbitrary independent structure-map parameter. -/
theorem independent_structure (X : Scheme.{u}) (n : ℕ) (r t : unitInterval)
    (x : (span X).space n) :
    (positiveSpan X).level (n + 1) (r, (span X).structureMap n x t) =
      (span (laurent.obj X)).structureMap n ((positiveSpan X).level n (r, x)) t :=
  (positiveSpan X).comm n r x t

end Consumer.GlobalRawBassInputCompositionSpan
