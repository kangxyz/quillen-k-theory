/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalSupportedRawCharts
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalSupportedRawRows

/-! # Genuine supported chart geometry and normalization regression properties -/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Bass AlgebraicGeometry.Scheme.PolynomialLaurent
open Quillen.PerfectComplexes Quillen.PerfectComplexes.GlobalSupportedRawBass
universe u
namespace QuillenTest.GlobalSupportedRawCharts

/-- Iterating polynomial geometry keeps the nested original global integer-base chart. -/
theorem nested_polynomial_chart (A : Scheme.QuasiCompactOpenPairs.{u}) :
    (Geometry.plus (pairPolynomialFunctor.obj A)).hom.right =
      GlobalIndex.plus.app (GlobalIndex.polynomial.obj A.obj.obj.right) := rfl

/-- A mixed polynomial/Laurent word retains the actual nested support pullback square. -/
theorem mixed_support_pullback (A : Scheme.QuasiCompactOpenPairs.{u}) :
    IsPullback (Geometry.laurent (pairPolynomialFunctor.obj A)).obj.hom
      (Geometry.laurentProjection (pairPolynomialFunctor.obj A)).hom.left
      (Geometry.laurentProjection (pairPolynomialFunctor.obj A)).hom.right
      (Geometry.polynomial A).obj.hom :=
  Geometry.laurent_isPullback (pairPolynomialFunctor.obj A)

/-- The two normalized raw chart composites compare through the same original Laurent map. -/
def chartCompositeComparison (A : Scheme.QuasiCompactOpenPairs.{u}) :
    (projectionMap A ≫ plusMap A).functor ≅ (projectionMap A ≫ minusMap A).functor :=
  (plusCompositionIso A).symm ≪≫ minusCompositionIso A

/-- A supported chart followed by its original normalization preserves the selected zero. -/
theorem chart_composite_zero (A : Scheme.QuasiCompactOpenPairs.{u}) :
    (projectionMap A ≫ plusMap A).functor.obj (rawModel A.obj).waldhausen.zero =
      (rawModel (Geometry.laurent A)).waldhausen.zero :=
  (projectionMap A ≫ plusMap A).zero

/-- Restriction acts on the complete Laurent support square, not just its ambient scheme. -/
theorem restriction_laurent_arrow {U X : Scheme.{u}} (j : U ⟶ X)
    [CompactSpace U] [CompactSpace X] (T : X.Opens) :
    (pairLaurentFunctor.map (Rows.restriction j T)).hom.hom =
      GlobalIndex.laurent.mapArrow.map (supportRestrictionPair j T).hom :=
  Geometry.laurent_map_arrow (Rows.restriction j T)

/-- The positive chart remains natural along the actual support-enlargement arrow. -/
theorem enlargement_plus_naturality {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    [CompactSpace X] (T : X.Opens) :
    pairLaurentFunctor.map (Rows.enlargement j T) ≫ pairPlus.app (Rows.source j T) =
      pairPlus.app (Rows.middle T) ≫ pairPolynomialFunctor.map (Rows.enlargement j T) :=
  pairPlus.naturality (Rows.enlargement j T)

end QuillenTest.GlobalSupportedRawCharts
