/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.TautologicalCoordinateCone
public import Aglib.AlgebraicGeometry.Spec.PolynomialLaurent.Coordinates
public import Mathlib.Data.ZMod.Basic

/-! The original signed cone is supported on the positive-chart complement, also over zero. -/
set_option autoImplicit false
set_option linter.mathlibStandardSet true
set_option warningAsError true

@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.Complex
open Quillen.PerfectComplexes Quillen.PerfectComplexes.ProjectiveLine
open AlgebraicGeometry.Scheme.ProjectiveLine AlgebraicGeometry.Scheme.Modules
universe u
namespace QuillenTest.TautologicalCoordinateCone

/-- The supported object retains the actual signed cone of the original single arrow. -/
theorem original_cone (R : CommRingCat.{u}) :
    (tautologicalCoordinateSupportedCone R).obj =
      CochainComplex.mappingCone
        ((CochainComplex.singleFunctor (twoChartLine R).Modules 0).map
          (tautologicalInclusionFirstProjection R)) := rfl

/-- Its actual positive restriction is acyclic in every cohomological degree. -/
private theorem positive_restriction_acyclic (R : CommRingCat.{u}) :
    ((restrict (plusChart R)).obj (tautologicalCoordinateSupportedCone R).obj).Acyclic :=
  (tautologicalCoordinateSupportedCone R).property.2

/-- The negative polynomial cone has the same cohomology through the actual chart cone iso. -/
private theorem negative_cone_homology (R : CommRingCat.{u}) (n : ℤ) :
    Nonempty
      (((HomologicalComplex.homologyFunctor (Spec (.of (Polynomial R))).Modules (.up ℤ) n).obj
          ((restrict (minusChart R)).obj (tautologicalCoordinateSupportedCone R).obj)) ≅
        ((HomologicalComplex.homologyFunctor (Spec (.of (Polynomial R))).Modules (.up ℤ) n).obj
          (CochainComplex.mappingCone
            ((CochainComplex.singleFunctor (Spec (.of (Polynomial R))).Modules 0).map
              (unitMul _ (polynomialCoordinate R)))))) :=
  ⟨(HomologicalComplex.homologyFunctor _ _ n).mapIso (tautologicalCoordinateConeMinusIso R)⟩

/-- The actual cone remains supported over the zero ring. -/
private theorem zero_ring_supported_cone :
    ((restrict (plusChart (.of (ZMod 1)))).obj
      (tautologicalCoordinateSupportedCone (.of (ZMod 1))).obj).Acyclic :=
  positive_restriction_acyclic _

open AlgebraicGeometry.Scheme.PolynomialLaurent in
/-- The chart cone is the unchanged original inverse-Laurent scalar cone, not a substitute. -/
private theorem negative_original_scalar_cone (R : CommRingCat.{u}) :
    Nonempty ((restrict (minusChart R)).obj (tautologicalCoordinateSupportedCone R).obj ≅
      (perfectOpenScalarCone (laurentMinus R) (polynomialGlobalCoordinate R)
        (laurentGlobalUnit R)⁻¹ (polynomialGlobalCoordinate_laurentMinus R)
        (rankOnePerfect (Spec (.of (Polynomial R))))).obj.obj) :=
  ⟨tautologicalCoordinateConeMinusGlobalScalarIso R⟩

end QuillenTest.TautologicalCoordinateCone
