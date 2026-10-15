/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenDeficitGradingStable

/-! Consumers retain the actual unshifted cone map and original face in signed degrees. -/
@[expose] public section

open Quillen.PerfectComplexes

noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
universe u
namespace QuillenTest.OpenDeficitGradingStable

open Quillen
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The unchanged cone map is bijective in degree zero without compactness assumptions. -/
theorem original_zero_bijective :
    Function.Bijective ((stableHomotopyFunctor 0).map (perfectOpenDeficitGradingMap j)) :=
  perfectOpenDeficitGradingMap_stable_zero_bijective j

/-- The actual target is concentrated, including all negative degrees. -/
theorem original_target_concentrated (d : ℤ) (hd : d ≠ 0) :
    Subsingleton (stableHomotopyGroup (perfectOpenDeficitGradedPrespectrum j) d) :=
  perfectOpenDeficitGradedPrespectrum_stable_subsingleton j d hd

/-- Its original inclusion face is still the unchanged change-of-weakness map in every degree. -/
theorem original_face (d : ℤ) :
    (stableHomotopyFunctor d).map (mappingConeInclusion (perfectOpenRestrictPrespectrumMap j)) ≫
      (stableHomotopyFunctor d).map (perfectOpenDeficitGradingMap j) =
        (stableHomotopyFunctor d).map (perfectOpenDeficitGradingChangeWeak j) := by
  exact ((stableHomotopyFunctor d).map_comp
    (mappingConeInclusion (perfectOpenRestrictPrespectrumMap j))
    (perfectOpenDeficitGradingMap j)).symm.trans
      (congrArg ((stableHomotopyFunctor d).map) (perfectOpenDeficitGradingMap_inclusion j))


variable [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace U]

/-- The actual original map, rather than an abstract group comparison, is invertible stably. -/
theorem original_map_isIso (d : ℤ) :
    IsIso ((stableHomotopyFunctor d).map (perfectOpenDeficitGradingMap j)) :=
  perfectOpenDeficitGradingMap_isStableEquivalence j d


end QuillenTest.OpenDeficitGradingStable
