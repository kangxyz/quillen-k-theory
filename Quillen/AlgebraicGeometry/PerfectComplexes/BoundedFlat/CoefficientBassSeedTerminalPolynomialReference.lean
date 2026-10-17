/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSeedTerminalInputReference
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSeedOriginalH0Reference

/-! The terminal original polynomial sheets retain both normalization routes. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.CoefficientBassSeedTerminalPolynomialReference
open BassMWholeNerve BassH0Merge
variable {R : CommRingCat.{u}} (P : Over (Spec R))

/-- The full projection square retains its two original binary normalizations. -/
def projectionIso {a b : Under R} (f : a ⟶ b) :
    (coefficientModel P f ≫ normalizedMap (polynomialProjection P b)).functor ≅
      (normalizedMap (polynomialProjection P a) ≫
        coefficientModel P ((polynomialUnderFunctor R).map f)).functor :=
  (BinaryNormalizationSimplex.total (polynomialProjection P b) (coefficientMap P f)).symm ≪≫
  eqToIso (congrArg (fun g ↦ (normalizedMap g).functor)
    (coefficientMap_naturality P (polynomialUnderCoefficient R) f).symm) ≪≫
  BinaryNormalizationSimplex.total
    (coefficientMap P ((polynomialUnderFunctor R).map f)) (polynomialProjection P a)

variable {a b : Under R} (f : a ⟶ b)
  (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)

/-- The postcomposed original polynomial sheet reference. -/
abbrev sourceReference := CoefficientBassPositiveC1BoundaryLift.polynomialReference P
  ((polynomialUnderCoefficient R).app a) (α.app a) ≫
    coefficientModel P ((polynomialUnderFunctor R).map ((laurentUnderFunctor R).map f))

/-- The source-precomposed original target polynomial sheet reference. -/
abbrev targetReference := coefficientModel P f ≫
  CoefficientBassPositiveC1BoundaryLift.polynomialReference P
    ((polynomialUnderCoefficient R).app b) (α.app b)

/-- The exact polynomial reference route through the genuine terminal input transport. -/
def referenceIso : (sourceReference P f α).functor ≅ (targetReference P f α).functor :=
  isoWhiskerRight
    (CoefficientBassSeedOriginalH0Reference.polynomialIso P
      ((polynomialUnderCoefficient R).app a) (α.app a)).symm
    (coefficientModel P
      ((polynomialUnderFunctor R).map ((laurentUnderFunctor R).map f))).functor ≪≫
  Functor.associator
    (CoefficientBassSeedCarrierLaurentReference.inputReference P
      ((polynomialUnderCoefficient R).app a) (α.app a)).functor
    (normalizedMap (polynomialProjection P ((laurentUnderFunctor R).obj a))).functor
    (coefficientModel P
      ((polynomialUnderFunctor R).map ((laurentUnderFunctor R).map f))).functor ≪≫
  isoWhiskerLeft
    (CoefficientBassSeedCarrierLaurentReference.inputReference P
      ((polynomialUnderCoefficient R).app a) (α.app a)).functor
    (projectionIso P ((laurentUnderFunctor R).map f)).symm ≪≫
  (Functor.associator
    (CoefficientBassSeedCarrierLaurentReference.inputReference P
      ((polynomialUnderCoefficient R).app a) (α.app a)).functor
    (coefficientModel P ((laurentUnderFunctor R).map f)).functor
    (normalizedMap (polynomialProjection P ((laurentUnderFunctor R).obj b))).functor).symm ≪≫
  isoWhiskerRight (CoefficientBassSeedTerminalInputReference.inputIso P f α)
    (normalizedMap (polynomialProjection P ((laurentUnderFunctor R).obj b))).functor ≪≫
  Functor.associator (coefficientModel P f).functor
    (CoefficientBassSeedCarrierLaurentReference.inputReference P
      ((polynomialUnderCoefficient R).app b) (α.app b)).functor
    (normalizedMap (polynomialProjection P ((laurentUnderFunctor R).obj b))).functor ≪≫
  isoWhiskerLeft (coefficientModel P f).functor
    (CoefficientBassSeedOriginalH0Reference.polynomialIso P
      ((polynomialUnderCoefficient R).app b) (α.app b))

end Quillen.PerfectComplexes.CoefficientBassSeedTerminalPolynomialReference
