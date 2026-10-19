/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterTensorReturnedInputSquare
import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterTensorReturnedTriangle

/-! # Actual geometric input and the specified tensor movement at each original section -/
noncomputable section
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open Quillen.PerfectComplexes Quillen.PerfectComplexes.ParameterTensorEvaluationRow
open Quillen.PerfectComplexes.GlobalSectionChangeIndex
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u
namespace QuillenTest.ParameterTensorModelInputSquare

/-- Arbitrary coefficient input preserves the entire genuine raw/evaluation movement square. -/
theorem actual_evaluation_routes (Q : Scheme.{u}) {X Y : Scheme.{u}ᵒᵖ} (g : X ⟶ Y)
    (K : (ParameterModels.ambient Q).obj X) :
    (rawEvaluatedInputIso Q g).hom.app K ≫ (modelEvaluationInputRight Q g).hom.app K =
      (modelEvaluationInputLeft Q g).hom.app K ≫
        (isoWhiskerRight (coefficientFunctorSquare (ParameterModels.ambient Q) g)
          (evaluationModel (op (scheme Q (laurent.op.obj Y)))).functor).hom.app K :=
  NatTrans.congr_app (congrArg Iso.hom (modelEvaluationInputSquare Q g).symm) K

/-- The return counit recovers the specified original movement, not merely its stable class. -/
theorem specified_return_movement (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ)
    (K : (ParameterModels.ambient Q).obj X) :
    (evaluationModel (op (scheme Q (laurent.op.obj X)))).functor.map
        ((returnedTensorIso Q X).hom.app K) ≫
      (returnedTensorEvaluationIso Q X).hom.app K = (internalTensorModelIso Q X).hom.app K :=
  NatTrans.congr_app (returnedTensorIso_evaluation Q X) K

/-- The entire evaluated returned square agrees with the independent raw tensor input square. -/
theorem returned_raw_input_routes (Q : Scheme.{u}) {X Y : Scheme.{u}ᵒᵖ} (g : X ⟶ Y)
    (K : (ParameterModels.ambient Q).obj X) :
    (rawEvaluatedInputIso Q g).hom.app K ≫
        (returnedEvaluationInputRight Q g).hom.app K =
      (returnedEvaluationInputLeft Q g).hom.app K ≫
        (isoWhiskerRight (returnedInputIso Q g)
          (evaluationModel (op (scheme Q (laurent.op.obj Y)))).functor).hom.app K :=
  NatTrans.congr_app (congrArg Iso.hom (returnedInputIso_evaluation_square Q g)) K

end QuillenTest.ParameterTensorModelInputSquare
