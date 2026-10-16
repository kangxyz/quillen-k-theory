/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.DerivedPushforwardVectorBundle
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.DerivedPerfect

/-! # Original derived projective-line coefficient consumers

These tests retain the original derived direct image, both ordinary triangle vertices,
the original connecting arrow, the explicit cone shift and the actual model map.
The nonreduced and zero-ring cases require only finite local freeness.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex

open Quillen.PerfectComplexes
open Quillen.PerfectComplexes.ProjectiveLine

noncomputable section
open CategoryTheory AlgebraicGeometry HomologicalComplex
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.ProjectiveLine
open AlgebraicGeometry.Scheme.PolynomialLaurent
universe u
namespace QuillenTest.ProjectiveLineDerivedCoefficient

open Quillen
/-- Use the standard derived category of original module sheaves. -/
local instance derivedCoefficientStandard (X : Scheme.{u}) :
    HasDerivedCategory.{u+1} X.Modules := HasDerivedCategory.standard _
variable (R : CommRingCat.{u}) (M : (twoChartLine R).Modules)

/-- Both ordinary terms of the original signed difference are fixed by identities. -/
theorem original_ordinary_vertices [M.IsQuasicoherent] :
    (derivedCechConeTriangleIso R M).hom.hom₁ = 𝟙 _ ∧
      (derivedCechConeTriangleIso R M).hom.hom₂ = 𝟙 _ :=
  ⟨derivedCechConeTriangleIso_hom_hom₁ R M,
    derivedCechConeTriangleIso_hom_hom₂ R M⟩

/-- The original derived connecting arrow is retained in the actual cone comparison. -/
theorem original_connecting [M.IsQuasicoherent] :
    ((DerivedCategory.Plus.ι.mapTriangle).obj (derivedCechTriangle R M)).mor₃ ≫
        (derivedCechConeTriangleIso R M).hom.hom₃ =
      (DerivedCategory.Q.mapTriangle.obj
        (CochainComplex.mappingCone.triangle
          ((single (Spec R).Modules (.up ℤ) 0).map
            ((Scheme.Modules.pushforward (projection R)).map
              (TwoOpen.sheafDifference (laurentPlus R) (laurentMinus R)
                (plusChart R) (minusChart R) (overlap_equation R) M))))).mor₂ :=
  derivedCechConeTriangleIso_connecting R M

/-- The actual comparison and its inverse give identity on the original derived direct image. -/
theorem original_derived_inverse [M.IsQuasicoherent] :
    (derivedCechConeIso R M).hom ≫ (derivedCechConeIso R M).inv = 𝟙 _ :=
  (derivedCechConeIso R M).hom_inv_id

/-- The model comparison uses the original derived Cech map and the actual forward chain map. -/
theorem original_model_map [M.IsQuasicoherent] (P : StrictPerfect (Spec R))
    (h : HomotopyEquiv (originalSheafCechComplex R M) P.obj) :
    (derivedCechStrictModelIso R M P h).hom =
      (derivedCechConeIso R M).hom ≫ DerivedCategory.Q.map h.hom := rfl

/-- An actual strict-perfect representative models the original derived direct image. -/
theorem original_strict_model [IsFiniteLocallyFree (twoChartLine R) M] :
    ∃ P : StrictPerfect (Spec R),
      Nonempty (DerivedCategory.Plus.ι.obj
          ((derivedPushforwardPlus (projection R)).obj
            ((DerivedCategory.Plus.singleFunctor (twoChartLine R).Modules 0).obj M)) ≅
        DerivedCategory.Q.obj P.obj) :=
  exists_derivedPushforward_vectorBundle_strict_model R M

/-- The original derived object satisfies the intrinsic perfect-object predicate. -/
theorem original_perfect [IsFiniteLocallyFree (twoChartLine R) M] :
    perfectDerivedObjects (Spec R)
      (DerivedCategory.Plus.ι.obj
        ((derivedPushforwardPlus (projection R)).obj
          ((DerivedCategory.Plus.singleFunctor (twoChartLine R).Modules 0).obj M))) :=
  perfect_derivedPushforward_vectorBundle R M

/-- Nonreduced coefficients need no regularity or noetherianity hypothesis. -/
theorem nonreduced_perfect (M : (twoChartLine (.of (ZMod 4))).Modules)
    [IsFiniteLocallyFree (twoChartLine (.of (ZMod 4))) M] :
    perfectDerivedObjects (Spec (.of (ZMod 4)))
      (DerivedCategory.Plus.ι.obj
        ((derivedPushforwardPlus (projection (.of (ZMod 4)))).obj
          ((DerivedCategory.Plus.singleFunctor (twoChartLine (.of (ZMod 4))).Modules 0).obj M))) :=
  perfect_derivedPushforward_vectorBundle _ M

/-- The zero-ring geometry retains the same original derived object. -/
theorem zero_ring_perfect (M : (twoChartLine (.of (ZMod 1))).Modules)
    [IsFiniteLocallyFree (twoChartLine (.of (ZMod 1))) M] :
    perfectDerivedObjects (Spec (.of (ZMod 1)))
      (DerivedCategory.Plus.ι.obj
        ((derivedPushforwardPlus (projection (.of (ZMod 1)))).obj
          ((DerivedCategory.Plus.singleFunctor (twoChartLine (.of (ZMod 1))).Modules 0).obj M))) :=
  perfect_derivedPushforward_vectorBundle _ M

end QuillenTest.ProjectiveLineDerivedCoefficient
