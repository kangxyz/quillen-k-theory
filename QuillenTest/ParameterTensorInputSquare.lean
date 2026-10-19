/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterTensorRawInput
import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterTensorReturnedInput

/-! # Actual coefficient-index squares retain the original tensor multiplication -/
noncomputable section
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open Quillen.PerfectComplexes Quillen.PerfectComplexes.ParameterTensorEvaluationRow
open Quillen.PerfectComplexes.GlobalSectionChangeIndex
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u
namespace QuillenTest.ParameterTensorInputSquare

/-- The source square uses the original product coefficient maps and the specified input arrow. -/
theorem original_projection_square (Q : Scheme.{u}) {X Y : Scheme.{u}ᵒᵖ} (g : X ⟶ Y) :
    inputSchemeMap Q (laurent.op.map g) ≫ coefficientMap Q X =
      coefficientMap Q Y ≫ inputSchemeMap Q g := coefficientMap_input Q g

/-- Every evaluated input retains the genuine forward tensor multiplication on the raw square. -/
theorem original_tensor_square (Q : Scheme.{u}) {X Y : Scheme.{u}ᵒᵖ} (g : X ⟶ Y)
    (K : BoundedFlatPerfect (scheme Q X)) :
    (boundedFlatPerfectPullback (inputSchemeMap Q (laurent.op.map g))).map
        ((boundedFlatPerfectTensorUnitPullbackAutomorphism (coefficientMap Q X)
          (ParameterLaurentUnit.projectedLaurentScalar Q X)).hom.app K) ≫
      (rawInputIso Q g).hom.app K =
    (rawInputIso Q g).hom.app K ≫
      (boundedFlatPerfectTensorUnitPullbackAutomorphism (coefficientMap Q Y)
        (ParameterLaurentUnit.projectedLaurentScalar Q Y)).hom.app
          ((boundedFlatPerfectPullback (inputSchemeMap Q g)).obj K) :=
  NatTrans.congr_app (rawInputIso_unit Q g) K

/-- The returned action has its own complete actual index square at every original section. -/
theorem returned_tensor_square (Q : Scheme.{u}) {X Y : Scheme.{u}ᵒᵖ} (g : X ⟶ Y)
    (K : (ParameterModels.ambient Q).obj X) :
    (((ParameterModels.ambient Q).map (laurent.op.map g)).functor).map
        ((returnedTensorUnit Q X).app K) ≫ (returnedInputIso Q g).hom.app K =
      (returnedInputIso Q g).hom.app K ≫
        (returnedTensorUnit Q Y).app (((ParameterModels.ambient Q).map g).functor.obj K) :=
  NatTrans.congr_app (returnedInputIso_unit Q g) K

end QuillenTest.ParameterTensorInputSquare
