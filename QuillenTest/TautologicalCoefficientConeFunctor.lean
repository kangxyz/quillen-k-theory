/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Tensor

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.TautologicalCoefficientConeFunctor
public import QuillenTest.MappingConeShortExact
public import QuillenTest.MappingConeWeakMap

/-! The exact supported functor retains the original object, map and degree-zero class. -/
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex
noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.PerfectComplexes Quillen.PerfectComplexes.ProjectiveLine
open AlgebraicGeometry.Scheme.ProjectiveLine
universe u
namespace QuillenTest.TautologicalCoefficientConeFunctor

/-- The functor object is the literal original supported coordinate cone. -/
theorem original_supported_object (R : CommRingCat.{u}) (K : Perfect (twoChartLine R)) :
    (tautologicalCoefficientConeFunctor R).obj K = tautologicalCoefficientSupportedCone R K :=
  tautologicalCoefficientConeFunctor_obj R K

/-- The actual supported map retains the original coordinate cone square. -/
theorem original_supported_map (R : CommRingCat.{u})
    {K L : Perfect (twoChartLine R)} (g : K ⟶ L) :
    ((tautologicalCoefficientConeFunctor R).map g).hom =
      CochainComplex.mappingCone.map
        (tautologicalCoefficientPerfectCoordinate R K).hom
        (tautologicalCoefficientPerfectCoordinate R L).hom
        ((AlgebraicGeometry.Scheme.Modules.Complex.tensorLeft (tautologicalLine R)).map g.hom) g.hom
        ((tautologicalCoefficientCoordinate R).naturality g.hom).symm :=
  tautologicalCoefficientConeFunctor_map_hom R g

/-- The genuine inherited Waldhausen structure is the one used by the cone K-map. -/
theorem original_supported_exact (R : CommRingCat.{u}) :
    Quillen.Waldhausen.IsExact (perfectWaldhausen (twoChartLine R)).cof
      (perfectWaldhausen (twoChartLine R)).weq
      (perfectSupportedWaldhausen (plusChart R)).cof
      (perfectSupportedWaldhausen (plusChart R)).weq (tautologicalCoefficientConeFunctor R) :=
  tautologicalCoefficientConeFunctor_waldhausenExact R

/-- The original K-zero functor map evaluates to the same previously fixed cone class. -/
theorem original_supported_object_class (R : CommRingCat.{u}) (K : Perfect (twoChartLine R)) :
    tautologicalCoefficientConeKMap R 0
        ((perfectWaldhausen (twoChartLine R)).kZeroObjectClass K) =
      (perfectSupportedWaldhausen (plusChart R)).kZeroObjectClass
        (tautologicalCoefficientSupportedCone R K) :=
  tautologicalCoefficientConeKMap_objectClass R K

end QuillenTest.TautologicalCoefficientConeFunctor
