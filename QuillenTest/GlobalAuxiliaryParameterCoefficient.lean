/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalAuxiliaryParameterCoefficientRestriction

/-! Regression for the complete original G7 supported-to-full-open Model composite. -/
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open Quillen.PerfectComplexes Quillen.PerfectComplexes.GlobalSectionChangeIndex
open GlobalAuxiliaryParameterCoefficient
universe u
variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))}
    (f : P ⟶ Q) [IsOpenImmersion f.left] (T : Q.left.Opens)

example :
    Functor.whiskerLeft specUnder
        (ParameterAuxiliarySupport.enlargement f.left T ≫
          ParameterAuxiliarySupport.restriction f.left T) ≫ openComparison f T =
      fiberComparison f T ≫
        (boundedFlatCoefficientSupportedFiberForgetModelTransformation f T ≫
          boundedFlatCoefficientSupportedOpenChangeWeakModelTransformation f T ≫
            boundedFlatCoefficientSupportedOpenRestrictionModelTransformation f T) := by
  rw [Functor.whiskerLeft_comp, Category.assoc, restriction_square,
    ← Category.assoc, enlargement_square, Category.assoc]

example (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    ((fiberComparison f T).app a).functor.obj
        ((ParameterAuxiliarySupport.fiber f.left T).obj (specUnder.obj a)).waldhausen.zero =
      (boundedFlatCoefficientSupportedFiberModel f T a).waldhausen.zero :=
  fiberComponent_zero f T a
