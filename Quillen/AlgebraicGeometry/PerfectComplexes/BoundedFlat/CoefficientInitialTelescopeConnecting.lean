/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientInitialEvaluationConnecting
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientFineFiberConnecting

/-!
# The original initial connecting map in the fine Bass telescope

The original stage-zero inclusions preserve both arrows of the initial
coefficient localization sequence and every time of its prescribed null.
Postcomposition by the original coarse-to-full-open telescope restriction gives
the actual full-open telescope null. Consequently the intrinsic initial fiber
boundary maps to the existing signed fine localization boundary in every
integer degree, without changing either boundary or choosing a new null.
-/
@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum

universe u

namespace Quillen.PerfectComplexes

variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left]

/-- The original supported inclusion gives the initial telescope's forgetful square. -/
theorem boundedFlatCoefficientInitialTelescope_forget (a : Under R) :
    (boundedFlatCoefficientSupportedForgetPrespectrumTransformation f).app a ≫
        (boundedFlatCoefficientAmbientBassTelescopeInclusion Q 0).app a =
      (boundedFlatCoefficientSupportedBassTelescopeInclusion f 0).app a ≫
        (boundedFlatCoefficientSupportedBassTelescopeForget f).app a :=
  (NatTrans.congr_app (boundedFlatCoefficientSupportedBassTelescopeInclusion_forget f 0) a).symm

/-- The original ambient stage-zero face retains the coarse-to-full-open restriction. -/
theorem boundedFlatCoefficientInitialTelescope_fullOpen (a : Under R) :
    (boundedFlatCoefficientAmbientBassTelescopeInclusion Q 0).app a ≫
        (boundedFlatCoefficientAmbientBassTelescopeFullOpen f).app a =
      (boundedFlatCoefficientAmbientOpenPrespectrumTransformation f).app a ≫
        ((boundedFlatCoefficientOpenBassTelescopeInclusion f 0).app a ≫
          (boundedFlatCoefficientOpenBassTelescopeRestriction f).app a) := by
  change (boundedFlatCoefficientAmbientBassTelescopeInclusion Q 0).app a ≫
      ((boundedFlatCoefficientAmbientBassTelescopeOpen f).app a ≫
        (boundedFlatCoefficientOpenBassTelescopeRestriction f).app a) = _
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun h ↦ h ≫ (boundedFlatCoefficientOpenBassTelescopeRestriction f).app a)
      (NatTrans.congr_app (boundedFlatCoefficientAmbientBassTelescopeInclusion_open f 0) a)).trans
        (Category.assoc _ _ _))

/-- Every original initial null value survives the same inclusion and full-open restriction. -/
theorem boundedFlatCoefficientInitialTelescope_fullOpenNull
    (a : Under R) (n : ℕ) (t : unitInterval)
    (x : ((boundedFlatCoefficientSupportedPrespectrumFunctor f).obj a).space n) :
    ((boundedFlatCoefficientOpenBassTelescopeInclusion f 0).app a ≫
        (boundedFlatCoefficientOpenBassTelescopeRestriction f).app a).map n
        (((boundedFlatCoefficientSupportedOpenDiagramNull f).homotopy a).level n (t, x)) =
      ((boundedFlatCoefficientSupportedBassTelescopeFullOpenNull f).homotopy a).level n
        (t, ((boundedFlatCoefficientSupportedBassTelescopeInclusion f 0).app a).map n x) := rfl

variable [CompactSpace P.left] [CompactSpace Q.left] [QuasiSeparatedSpace Q.left]

/-- The initial intrinsic boundary enters the existing fine boundary through the original maps. -/
theorem boundedFlatCoefficientInitialConnecting_telescope (a : Under R) (d : ℤ) :
    let := boundedFlatCoefficientInitialFiberLift_isStableEquivalence f a d
    stableFiberLiftConnecting
        ((boundedFlatCoefficientSupportedForgetPrespectrumTransformation f).app a)
        ((boundedFlatCoefficientAmbientOpenPrespectrumTransformation f).app a)
        ((boundedFlatCoefficientSupportedOpenDiagramNull f).homotopy a) d ≫
        (stableHomotopyFunctor d).map
          ((boundedFlatCoefficientSupportedBassTelescopeInclusion f 0).app a) =
      (stableHomotopyFunctor (d + 1)).map
          ((boundedFlatCoefficientOpenBassTelescopeInclusion f 0).app a ≫
            (boundedFlatCoefficientOpenBassTelescopeRestriction f).app a) ≫
        boundedFlatCoefficientFineLocalizationConnecting f a d := by
  let := boundedFlatCoefficientInitialFiberLift_isStableEquivalence f a d
  let : IsIso ((stableHomotopyFunctor d).map
      (homotopyFiberLift ((boundedFlatCoefficientAmbientBassTelescopeFullOpen f).app a)
        ((boundedFlatCoefficientSupportedBassTelescopeForget f).app a)
        ((boundedFlatCoefficientSupportedBassTelescopeFullOpenNull f).homotopy a))) :=
    boundedFlatCoefficientSupportedBassTelescopeFullOpenFiberMap_isStableEquivalence f a d
  rw [boundedFlatCoefficientFineLocalizationConnecting_eq_fiberLift]
  exact stableFiberLiftConnecting_naturality
    ((boundedFlatCoefficientSupportedForgetPrespectrumTransformation f).app a)
    ((boundedFlatCoefficientAmbientOpenPrespectrumTransformation f).app a)
    ((boundedFlatCoefficientSupportedBassTelescopeForget f).app a)
    ((boundedFlatCoefficientAmbientBassTelescopeFullOpen f).app a)
    ((boundedFlatCoefficientSupportedOpenDiagramNull f).homotopy a)
    ((boundedFlatCoefficientSupportedBassTelescopeFullOpenNull f).homotopy a)
    ((boundedFlatCoefficientSupportedBassTelescopeInclusion f 0).app a)
    ((boundedFlatCoefficientAmbientBassTelescopeInclusion Q 0).app a)
    ((boundedFlatCoefficientOpenBassTelescopeInclusion f 0).app a ≫
      (boundedFlatCoefficientOpenBassTelescopeRestriction f).app a)
    (boundedFlatCoefficientInitialTelescope_forget f a)
    (boundedFlatCoefficientInitialTelescope_fullOpen f a)
    (boundedFlatCoefficientInitialTelescope_fullOpenNull f a) d

end Quillen.PerfectComplexes
