/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterTensorReturnedTriangle

/-! # Original moving comparison recovered through the actual normalized inverse -/
noncomputable section
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open Quillen.PerfectComplexes
open ParameterTensorEvaluationRow GlobalSectionChangeIndex
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u

example (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :
    whiskerRight (returnedTensorIso Q X).hom
        (evaluationModel (op (scheme Q (laurent.op.obj X)))).functor ≫
      (returnedTensorEvaluationIso Q X).hom = (internalTensorModelIso Q X).hom :=
  returnedTensorIso_evaluation Q X

example (X : Scheme.{u}ᵒᵖ) (A : globalModel.obj X) :
    (evaluationModel X).functor.map ((evaluationInverseUnit X).inv.app A) ≫
      (evaluationInverseCounit X).hom.app ((evaluationModel X).functor.obj A) =
        𝟙 ((evaluationModel X).functor.obj A) :=
  Quillen.Waldhausen.IteratedS.ExactModelEquivalence.forward_unit_counit
    (evaluationModelEquivalence X) (evaluationModel X).exact
    (evaluationSmallEquivalence_inverse_exact X) (evaluationModel X).zero A
