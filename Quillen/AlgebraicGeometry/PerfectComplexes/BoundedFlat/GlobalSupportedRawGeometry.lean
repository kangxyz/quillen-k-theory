/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Spec.PolynomialLaurent.IndexSquare
public import Quillen.Aglib.AlgebraicGeometry.Spec.PolynomialLaurent.OpenPairZeroSection

/-!
# Existing quasi-compact support pairs in the original global Bass convention

The polynomial and Laurent pairs and all four arrows are the existing `Scheme.Bass`
constructions, viewed in `Scheme.OpenPairs`. Their entire underlying arrows are the original
`GlobalIndex` products and charts. The original inverse-image pullback squares are retained.
Only the ambient scheme is required quasi-compact; no compactness of the support open is used.
This is geometry for the supported raw base, not a raw cone, loop or seed construction.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Products AlgebraicGeometry.Scheme.Bass
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace Quillen.PerfectComplexes.GlobalSupportedRawBass.Geometry

/-- The existing polynomial pair, forgetting only ambient quasi-compactness. -/
abbrev polynomial (A : Scheme.QuasiCompactOpenPairs.{u}) : Scheme.OpenPairs.{u} :=
  Scheme.quasiCompactOpenPairsInclusion.obj (pairPolynomialFunctor.obj A)

/-- The existing Laurent pair, forgetting only ambient quasi-compactness. -/
abbrev laurent (A : Scheme.QuasiCompactOpenPairs.{u}) : Scheme.OpenPairs.{u} :=
  Scheme.quasiCompactOpenPairsInclusion.obj (pairLaurentFunctor.obj A)

/-- The unchanged polynomial projection as an actual open-pair square. -/
abbrev projection (A : Scheme.QuasiCompactOpenPairs.{u}) : polynomial A ⟶ A.obj :=
  Scheme.quasiCompactOpenPairsInclusion.map (pairPolynomialProjection.app A)

/-- The unchanged Laurent projection as an actual open-pair square. -/
abbrev laurentProjection (A : Scheme.QuasiCompactOpenPairs.{u}) : laurent A ⟶ A.obj :=
  Scheme.quasiCompactOpenPairsInclusion.map (pairLaurentProjection.app A)

/-- The existing positive chart on both entries of the pair. -/
abbrev plus (A : Scheme.QuasiCompactOpenPairs.{u}) : laurent A ⟶ polynomial A :=
  Scheme.quasiCompactOpenPairsInclusion.map (pairPlus.app A)

/-- The existing inverse-coordinate chart on both entries of the pair. -/
abbrev minus (A : Scheme.QuasiCompactOpenPairs.{u}) : laurent A ⟶ polynomial A :=
  Scheme.quasiCompactOpenPairsInclusion.map (pairMinus.app A)

open AlgebraicGeometry.Scheme.PolynomialLaurent

/-- The entire polynomial open immersion is the actual original global product arrow. -/
theorem polynomial_arrow (A : Scheme.QuasiCompactOpenPairs.{u}) :
    (polynomial A).obj = GlobalIndex.polynomial.mapArrow.obj A.obj.obj := rfl

/-- The entire Laurent open immersion is the actual original global product arrow. -/
theorem laurent_arrow (A : Scheme.QuasiCompactOpenPairs.{u}) :
    (laurent A).obj = GlobalIndex.laurent.mapArrow.obj A.obj.obj := rfl

/-- Every polynomial pair morphism retains both original global product maps. -/
theorem polynomial_map_arrow {A B : Scheme.QuasiCompactOpenPairs.{u}} (f : A ⟶ B) :
    (pairPolynomialFunctor.map f).hom.hom = GlobalIndex.polynomial.mapArrow.map f.hom.hom := rfl

/-- Every Laurent pair morphism retains both original global product maps. -/
theorem laurent_map_arrow {A B : Scheme.QuasiCompactOpenPairs.{u}} (f : A ⟶ B) :
    (pairLaurentFunctor.map f).hom.hom = GlobalIndex.laurent.mapArrow.map f.hom.hom := rfl

/-- Both entries and the commutative square are the original positive global chart. -/
theorem plus_arrow (A : Scheme.QuasiCompactOpenPairs.{u}) :
    (plus A).hom = ((Functor.mapArrowFunctor _ _).map GlobalIndex.plus).app A.obj.obj := rfl

/-- Both entries and the commutative square are the original inverse global chart. -/
theorem minus_arrow (A : Scheme.QuasiCompactOpenPairs.{u}) :
    (minus A).hom = ((Functor.mapArrowFunctor _ _).map GlobalIndex.minus).app A.obj.obj := rfl

/-- Both projection entries are precisely the original global polynomial projections. -/
theorem projection_arrow (A : Scheme.QuasiCompactOpenPairs.{u}) :
    (projection A).hom =
      ((Functor.mapArrowFunctor _ _).map GlobalIndex.projection).app A.obj.obj := rfl

/-- The Laurent projection is the same first projection from the integer-base product. -/
theorem laurentProjection_arrow (A : Scheme.QuasiCompactOpenPairs.{u}) :
    (laurentProjection A).hom = ((Functor.mapArrowFunctor _ _).map
      (baseProductProjection (AlgebraicGeometry.Scheme.PolynomialLaurent.laurentProjection
        (.of (ULift.{u} ℤ))))).app
        A.obj.obj := rfl

/-- The positive projection triangle is the original equality of whole pair morphisms. -/
@[reassoc]
theorem plus_projection (A : Scheme.QuasiCompactOpenPairs.{u}) :
    plus A ≫ projection A = laurentProjection A :=
  congrArg Scheme.quasiCompactOpenPairsInclusion.map (pairPlus_projection A)

/-- The inverse-coordinate triangle retains the same literal Laurent projection. -/
@[reassoc]
theorem minus_projection (A : Scheme.QuasiCompactOpenPairs.{u}) :
    minus A ≫ projection A = laurentProjection A :=
  congrArg Scheme.quasiCompactOpenPairsInclusion.map (pairMinus_projection A)

/-- The polynomial support open is the actual inverse image under the original projection. -/
theorem polynomial_isPullback (A : Scheme.QuasiCompactOpenPairs.{u}) :
    IsPullback (polynomial A).obj.hom (projection A).hom.left
      (projection A).hom.right A.obj.obj.hom :=
  baseProductFunctor_map_isPullback _ A.obj.obj.hom

/-- The Laurent support open is the actual inverse image under the original projection. -/
theorem laurent_isPullback (A : Scheme.QuasiCompactOpenPairs.{u}) :
    IsPullback (laurent A).obj.hom (laurentProjection A).hom.left
      (laurentProjection A).hom.right A.obj.obj.hom :=
  baseProductFunctor_map_isPullback _ A.obj.obj.hom

end Quillen.PerfectComplexes.GlobalSupportedRawBass.Geometry
