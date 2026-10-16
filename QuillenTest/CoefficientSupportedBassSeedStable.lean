/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportedBassSeedStable

/-! Original supported/ambient seed clients use the actual supplied geometric Model actions. -/
public section
noncomputable section
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen Quillen.LoopPrespectrum
open CommRingCat.PolynomialLaurent Quillen.PerfectComplexes Quillen.KTheory.Bass
universe u
namespace QuillenTest.CoefficientSupportedBassSeedStable
attribute [local irreducible] boundedFlatCoefficientSupportedModelFunctor
  boundedFlatCoefficientSectionModelRow Quillen.Waldhausen.IteratedS.prespectrumFunctor
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q) [IsOpenImmersion f.left]

theorem original_supported_seed (a : Under R) (d : ℤ) :
    (stableHomotopyFunctor d).map ((boundedFlatCoefficientSupportedBassSeed f).app a) =
      ((boundedFlatCoefficientSupportedLaurentAction f).track.homotopy a).stableOperation d ≫
        (stableHomotopyFunctor (d + 1)).map
          (mappingConeInclusion (StrictSquare.comparison
            (LaurentSeed.square (boundedFlatCoefficientSupportedPrespectrumFunctor f) a))) ≫
              (parameterStableHomotopyIso
                (LaurentSeed.cone (boundedFlatCoefficientSupportedPrespectrumFunctor f) a) d).inv :=
  boundedFlatCoefficientSupportedBassSeed_stableHomotopy_eq f a d

theorem original_supported_stage (a : Under R) (d : ℤ) (n : ℕ) :
    stableHomotopyι ((boundedFlatCoefficientSupportedPrespectrumFunctor f).obj a) d n ≫
      (stableHomotopyFunctor d).map ((boundedFlatCoefficientSupportedBassSeed f).app a) ≫
        (parameterStableHomotopyIso
          (LaurentSeed.cone (boundedFlatCoefficientSupportedPrespectrumFunctor f) a) d).hom =
      ((-1 : ℤ) ^ n •
        Homotopy.stableStageOperation
          ((boundedFlatCoefficientSupportedLaurentAction f).track.homotopy a) d n) ≫
        (shiftedStableReindexIso ((boundedFlatCoefficientSupportedPrespectrumFunctor f).obj
          ((laurentUnderFunctor R).obj a)) d n).hom ≫
          stableHomotopyι ((boundedFlatCoefficientSupportedPrespectrumFunctor f).obj
            ((laurentUnderFunctor R).obj a)) (d + 1) (parameterStableOffset d + n) ≫
              (stableHomotopyFunctor (d + 1)).map
                (mappingConeInclusion (StrictSquare.comparison
                  (LaurentSeed.square (boundedFlatCoefficientSupportedPrespectrumFunctor f) a))) :=
  (boundedFlatCoefficientSupportedLaurentAction f).track.seedMap_stableHomotopy_ι a d n

theorem original_ambient_seed (Q : Over (Spec R)) (a : Under R) (d : ℤ) :
    (stableHomotopyFunctor d).map ((boundedFlatCoefficientAmbientBassSeed Q).app a) =
      ((boundedFlatCoefficientAmbientLaurentAction Q).track.homotopy a).stableOperation d ≫
        (stableHomotopyFunctor (d + 1)).map
          (mappingConeInclusion (StrictSquare.comparison
            (LaurentSeed.square (boundedFlatCoefficientAmbientPrespectrumFunctor Q) a))) ≫
              (parameterStableHomotopyIso
                (LaurentSeed.cone (boundedFlatCoefficientAmbientPrespectrumFunctor Q) a) d).inv :=
  boundedFlatCoefficientAmbientBassSeed_stableHomotopy_eq Q a d

end QuillenTest.CoefficientSupportedBassSeedStable
