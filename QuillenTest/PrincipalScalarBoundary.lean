/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Quillen.GTheory.FiniteModules.PrincipalObjectBoundary
import Quillen.KTheory.LowDegreeScalarAction.DvrSymbols
import Quillen.KTheory.LowDegreeScalarAction.UniverseNaturality

/-! Consumer checks for the original positive principal boundary and its field-product lowering.
No unit-uniformizer boundary computation or Milnor marking is asserted here. -/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open Quillen.FiniteModuleLocalization Quillen.FiniteModuleLocalization.PrincipalObjectBoundary
open FGModuleCat.PrincipalRankOne Quillen.LowDegreeScalarAction
open scoped nonZeroDivisors
universe u

namespace QuillenTest.PrincipalScalarBoundary

/-- The original positive rank-one scalar cube at 2 has the original closed-boundary value. -/
theorem integerTwoBoundary :
    closedConnectingHom (2 : ℤ) 0
      (Quotient.mk' (Quillen.Automorphism.Cube.automorphismFirstCube
        (ModuleCat.finiteModuleExactStructure.{0, 0} (Localization.Away (2 : ℤ))).smallModel
        (smallRankOne (Localization.Away (2 : ℤ))) (smallLocalizationAut ℤ 2))) =
    (ModuleCat.finiteModuleExactStructure.{0, 0} (ClosedRing (2 : ℤ))).smallModel.kZeroObjectClass
      (smallRankOne (ClosedRing (2 : ℤ))) :=
  closedConnectingHom_positiveRankOne ℤ 2 (by simp)

/-- The original closed boundary is neutral for the unit principal element 1. -/
theorem unitOneBoundary :
    closedConnectingHom (1 : ℤ) 0
      (Quotient.mk' (Quillen.Automorphism.Cube.automorphismFirstCube
        (ModuleCat.finiteModuleExactStructure.{0, 0} (Localization.Away (1 : ℤ))).smallModel
        (smallRankOne (Localization.Away (1 : ℤ))) (smallLocalizationAut ℤ 1))) = 1 :=
  closedConnectingHom_positiveRankOne_of_isUnit ℤ 1 isUnit_one

/-- Lowering the existing upper FieldSymbols product retains the original lower positive cube. -/
theorem loweredFieldProduct (F : Type u) [Field F] (a b : Fˣ) :
    DvrSymbols.loweredUnitProduct F a b =
      ScalarUnit.smallModelKOneAction.{u, u + 1, u, u} F
        (ModuleCat.finiteModuleExactStructure.{u, u} F) a
        (Quotient.mk' (Quillen.Automorphism.Cube.automorphismFirstCube
          (ModuleCat.finiteModuleExactStructure.{u, u} F).smallModel.{u}
          ((equivSmallModel.{u} (FGModuleCat.{u} F)).functor.obj
            (FGModuleCat.of F (Fin 1 → F)))
          ((equivSmallModel.{u} (FGModuleCat.{u} F)).functor.mapIso
            (FGModuleCat.matrixToAut F 1
              (Matrix.GeneralLinearGroup.scalar (Fin 1) b))))) := by
  rw [DvrSymbols.loweredUnitProduct_field,
    UniverseNaturality.field_unitProduct_eq_lowerScalarCubeAction]

end QuillenTest.PrincipalScalarBoundary
