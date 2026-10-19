/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalSupportedRawCharts
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalSupportedRawRows

/-! # External use of the three genuine supported integer-base chart rows -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Bass
open Quillen.PerfectComplexes Quillen.PerfectComplexes.GlobalSupportedRawBass
open Quillen.PerfectComplexes.GlobalSectionChangeIndex
open Quillen.PerfectComplexes.SupportedTensorEvaluation
universe u
namespace Consumer.GlobalSupportedRawCharts

/-- A client obtains the original raw evaluation edge on the actual localized row. -/
def evaluationOnTarget {U X : Scheme.{u}} (j : U ⟶ X)
    [CompactSpace U] (T : X.Opens) :
    (supportedPairModelMap (Geometry.minus (Rows.target j T)) ≫
      evaluationModel (X := op (Geometry.laurent (Rows.target j T)).obj.right)
        (Geometry.laurent (Rows.target j T)).obj.hom).functor ≅
    (evaluationModel (X := op (Geometry.polynomial (Rows.target j T)).obj.right)
        (Geometry.polynomial (Rows.target j T)).obj.hom ≫
      minusMap (Rows.target j T)).functor :=
  minusEvaluationIso (Rows.target j T)

/-- The union-support row has both genuine chart composites, at a mixed nested product. -/
def mixedRowChartComparison {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    [CompactSpace X] (T : X.Opens) :
    let A := pairLaurentFunctor.obj (pairPolynomialFunctor.obj (Rows.source j T))
    (projectionMap A ≫ plusMap A).functor ≅ (projectionMap A ≫ minusMap A).functor :=
  (plusCompositionIso _).symm ≪≫ minusCompositionIso _

/-- The existing pair category closes under both row arrows and their polynomial composite. -/
theorem polynomial_rows_compose {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    [CompactSpace U] [CompactSpace X] (T : X.Opens) :
    pairPolynomialFunctor.map (Rows.restriction j T ≫ Rows.enlargement j T) =
      pairPolynomialFunctor.map (Rows.restriction j T) ≫
        pairPolynomialFunctor.map (Rows.enlargement j T) :=
  Rows.polynomial_row_comp j T

end Consumer.GlobalSupportedRawCharts
