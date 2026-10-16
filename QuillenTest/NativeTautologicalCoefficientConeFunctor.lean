/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.NativeTautologicalCoefficientConeFunctor

/-! Original native cone components, arbitrary coefficient maps and all-degree K-map clients. -/
public section
noncomputable section
open AlgebraicGeometry.Scheme.Modules.Complex
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.PerfectComplexes
open Quillen.PerfectComplexes.ProjectiveLine Quillen.PerfectComplexes.ProjectiveLine.BassPositive
open AlgebraicGeometry.Scheme.ProjectiveLine
  AlgebraicGeometry.Scheme.PolynomialLaurent
universe u
namespace QuillenTest.NativeTautologicalCoefficientConeFunctor

/-- The actual natural-iso component is the previously fixed supported cone isomorphism. -/
theorem original_component (R : CommRingCat.{u}) (K : Perfect (twoChartLine R)) :
    (nativeTautologicalCoefficientConeMinusNatIso R).app K =
      nativeTautologicalCoefficientSupportedConeMinusIso R K :=
  nativeTautologicalCoefficientConeMinusNatIso_app R K

/-- Arbitrary perfect coefficient arrows keep the literal inverse-affine restriction. -/
theorem original_arrow (R : CommRingCat.{u}) {K L : Perfect (twoChartLine R)} (g : K ⟶ L) :
    ((nativeTautologicalCoefficientConeFunctor R).map g).hom =
      (restrict (nativeAffineIso R).inv).map
        ((tautologicalCoefficientConeFunctor R).map g).hom :=
  nativeTautologicalCoefficientConeFunctor_map_hom R g

/-- Every original connective class uses the same actual restriction and scalar-cone maps. -/
theorem original_restriction (R : CommRingCat.{u}) (n : ℕ) (x : PerfectK (twoChartLine R) n) :
    perfectSupportedKRestrict (affineNativeChart R false) (positiveOpen R) n
        (nativeTautologicalCoefficientConeKMap R n x) =
      perfectSupportedScalarConeKMap (overlapOpen R).ι
        (polynomialGlobalCoordinate R) (overlapLaurentGlobalUnit R)⁻¹
        (polynomialGlobalCoordinate_overlap R) n (perfectKRestrict (minusChart R) n x) :=
  DFunLike.congr_fun (nativeTautologicalCoefficientConeKMap_restrict R n) x

/-- Degree zero retains the original cone object rather than a newly chosen class map. -/
theorem original_object_class (R : CommRingCat.{u}) (K : Perfect (twoChartLine R)) :
    nativeTautologicalCoefficientConeKMap R 0
        ((perfectWaldhausen (twoChartLine R)).kZeroObjectClass K) =
      (perfectSupportedWaldhausen (positiveOpen R).ι).kZeroObjectClass
        (nativeTautologicalCoefficientSupportedCone R K) :=
  nativeTautologicalCoefficientConeKMap_objectClass R K

end QuillenTest.NativeTautologicalCoefficientConeFunctor
