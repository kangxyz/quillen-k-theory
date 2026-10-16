/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.KTheory.Bass.StrictLaurentSeedStable

/-! The original strict natural-transformation component retains its actual cone and tail. -/
public section
noncomputable section
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Quillen Quillen.LoopPrespectrum CommRingCat.PolynomialLaurent
open Quillen.KTheory.Bass.LaurentSeed
universe u w
namespace QuillenTest.StrictLaurentSeedStable
variable {R : CommRingCat.{u}} {F : Under R ⥤ LoopPrespectrum.{w}} (A : Track F)

theorem original_seed_component (a : Under R) (d : ℤ) :
    (stableHomotopyFunctor d).map (A.seed.app a) =
      (A.homotopy a).stableOperation d ≫
        (stableHomotopyFunctor (d + 1)).map
          (mappingConeInclusion (StrictSquare.comparison (square F a))) ≫
            (parameterStableHomotopyIso (cone F a) d).inv :=
  A.seedMap_stableHomotopy_eq a d

theorem original_negative_tail (a : Under R) (n : ℕ) :
    stableHomotopyι (F.obj a) (-1) n ≫ (stableHomotopyFunctor (-1)).map (A.seed.app a) ≫
        (parameterStableHomotopyIso (cone F a) (-1)).hom =
      ((-1 : ℤ) ^ n • (A.homotopy a).stableStageOperation (-1) n) ≫
        (shiftedStableReindexIso (F.obj ((laurentUnderFunctor R).obj a)) (-1) n).hom ≫
          stableHomotopyι (F.obj ((laurentUnderFunctor R).obj a)) ((-1 : ℤ) + 1)
            (parameterStableOffset (-1) + n) ≫
            (stableHomotopyFunctor ((-1 : ℤ) + 1)).map
              (mappingConeInclusion (StrictSquare.comparison (square F a))) :=
  A.seedMap_stableHomotopy_ι a (-1) n

theorem original_negative_tail_offset : parameterStableOffset (-1) = 1 := rfl

end QuillenTest.StrictLaurentSeedStable
