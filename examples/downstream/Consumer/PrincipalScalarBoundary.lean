/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Quillen.GTheory.FiniteModules.PrincipalObjectBoundary
import Quillen.KTheory.LowDegreeScalarAction.DvrSymbols
import Quillen.KTheory.LowDegreeScalarAction.UniverseNaturality
import Mathlib.RingTheory.PowerSeries.Inverse

/-! Independent client checks for the original boundary and scalar-action lowering interfaces.
No unit-uniformizer boundary computation or Milnor marking is asserted here. -/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open Quillen.FiniteModuleLocalization Quillen.FiniteModuleLocalization.PrincipalObjectBoundary
open FGModuleCat.PrincipalRankOne Quillen.LowDegreeScalarAction
open scoped nonZeroDivisors

namespace Consumer.PrincipalScalarBoundary

universe u

/-- The literal integer-2 positive scalar cube reaches the original quotient object class. -/
theorem integerTwoBoundary :
    closedConnectingHom (2 : ℤ) 0
      (Quotient.mk' (Quillen.Automorphism.Cube.automorphismFirstCube
        (ModuleCat.finiteModuleExactStructure.{0, 0} (Localization.Away (2 : ℤ))).smallModel
        (smallRankOne (Localization.Away (2 : ℤ))) (smallLocalizationAut ℤ 2))) =
    (ModuleCat.finiteModuleExactStructure.{0, 0} (ClosedRing (2 : ℤ))).smallModel.kZeroObjectClass
      (smallRankOne (ClosedRing (2 : ℤ))) :=
  closedConnectingHom_positiveRankOne ℤ 2 (by simp)

/-- The upper field product lowers to the stated original lower scalar cube action. -/
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

/-- A concrete power-series module tests scalar-action naturality across the chosen models. -/
theorem powerSeriesScalarUniverse (a : (PowerSeries ℚ)ˣ)
    (z : Quillen.FiniteModuleLocalization.G (PowerSeries ℚ) 1) :
    (ModuleCat.finiteModuleExactStructure (PowerSeries ℚ)).smallKUniverseEquiv.{0, 1} 2
        (ScalarUnit.smallModelKOneAction.{0, 1, 0, 0} (PowerSeries ℚ)
          (ModuleCat.finiteModuleExactStructure (PowerSeries ℚ)) a z) =
      ScalarUnit.upperFiniteModuleKOneAction (PowerSeries ℚ) a
        ((ModuleCat.finiteModuleExactStructure (PowerSeries ℚ)).smallKUniverseEquiv.{0, 1} 1 z) :=
  UniverseNaturality.finiteModule_kOneAction_universe (PowerSeries ℚ) a z

end Consumer.PrincipalScalarBoundary
