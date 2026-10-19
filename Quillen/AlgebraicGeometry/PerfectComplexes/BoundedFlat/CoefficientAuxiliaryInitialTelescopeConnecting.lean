/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientAuxiliaryInitialConnecting
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientAuxiliaryFiberConnecting

/-!
# The original initial connecting map in the auxiliary-support Bass telescope

The original stage-zero inclusions preserve both arrows of the initial
auxiliary-supported localization sequence and every time of its prescribed null.
Postcomposition by the original coarse-to-full-open telescope restriction gives
the actual full-open telescope null. Consequently the intrinsic initial fiber
boundary maps to the existing signed auxiliary localization boundary in every
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
  [IsOpenImmersion f.left] (T : Q.left.Opens)

/-- The original supported inclusion gives the initial telescope's forgetful square. -/
theorem boundedFlatCoefficientAuxiliaryInitialTelescope_forget (a : Under R) :
    (boundedFlatCoefficientSupportedFiberForgetPrespectrumTransformation f T).app a ≫
        (boundedFlatCoefficientSupportedAmbientBassTelescopeInclusion T 0).app a =
      (boundedFlatCoefficientSupportedFiberBassTelescopeInclusion f T 0).app a ≫
        (boundedFlatCoefficientSupportedFiberBassTelescopeForget f T).app a :=
  (NatTrans.congr_app
    (boundedFlatCoefficientSupportedFiberBassTelescopeInclusion_forget f T 0) a).symm

omit [IsOpenImmersion f.left] in
/-- The original ambient stage-zero face retains the coarse-to-full-open restriction. -/
theorem boundedFlatCoefficientAuxiliaryInitialTelescope_fullOpen (a : Under R) :
    (boundedFlatCoefficientSupportedAmbientBassTelescopeInclusion T 0).app a ≫
        (boundedFlatCoefficientSupportedAmbientBassTelescopeFullOpen f T).app a =
      (boundedFlatCoefficientSupportedAmbientOpenPrespectrumTransformation f T).app a ≫
        ((boundedFlatCoefficientSupportedOpenBassTelescopeInclusion f T 0).app a ≫
          (boundedFlatCoefficientSupportedOpenBassTelescopeRestriction f T).app a) := by
  change (boundedFlatCoefficientSupportedAmbientBassTelescopeInclusion T 0).app a ≫
      ((boundedFlatCoefficientSupportedAmbientBassTelescopeOpen f T).app a ≫
        (boundedFlatCoefficientSupportedOpenBassTelescopeRestriction f T).app a) = _
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun h ↦ h ≫ (boundedFlatCoefficientSupportedOpenBassTelescopeRestriction f T).app a)
      (NatTrans.congr_app
        (boundedFlatCoefficientSupportedAmbientBassTelescopeInclusion_open f T 0) a)).trans
        (Category.assoc _ _ _))

/-- Every original initial null value survives the same inclusion and full-open restriction. -/
theorem boundedFlatCoefficientAuxiliaryInitialTelescope_fullOpenNull
    (a : Under R) (n : ℕ) (t : unitInterval)
    (x : ((boundedFlatCoefficientSupportedFiberPrespectrumFunctor f T).obj a).space n) :
    ((boundedFlatCoefficientSupportedOpenBassTelescopeInclusion f T 0).app a ≫
        (boundedFlatCoefficientSupportedOpenBassTelescopeRestriction f T).app a).map n
        (((boundedFlatCoefficientSupportedFiberOpenDiagramNull f T).homotopy a).level n (t, x)) =
      ((boundedFlatCoefficientSupportedFiberBassTelescopeFullOpenNull f T).homotopy a).level n
        (t, ((boundedFlatCoefficientSupportedFiberBassTelescopeInclusion f T 0).app a).map n x) :=
  rfl

variable [CompactSpace P.left] [CompactSpace Q.left] [QuasiSeparatedSpace Q.left] [CompactSpace T]

/-- The initial intrinsic boundary enters the existing fine boundary through the original maps. -/
theorem boundedFlatCoefficientAuxiliaryInitialConnecting_telescope (a : Under R) (d : ℤ) :
    let := boundedFlatCoefficientAuxiliaryInitialFiberLift_isStableEquivalence f T a d
    stableFiberLiftConnecting
        ((boundedFlatCoefficientSupportedFiberForgetPrespectrumTransformation f T).app a)
        ((boundedFlatCoefficientSupportedAmbientOpenPrespectrumTransformation f T).app a)
        ((boundedFlatCoefficientSupportedFiberOpenDiagramNull f T).homotopy a) d ≫
        (stableHomotopyFunctor d).map
          ((boundedFlatCoefficientSupportedFiberBassTelescopeInclusion f T 0).app a) =
      (stableHomotopyFunctor (d + 1)).map
          ((boundedFlatCoefficientSupportedOpenBassTelescopeInclusion f T 0).app a ≫
            (boundedFlatCoefficientSupportedOpenBassTelescopeRestriction f T).app a) ≫
        boundedFlatCoefficientAuxiliaryLocalizationConnecting f T a d := by
  let := boundedFlatCoefficientAuxiliaryInitialFiberLift_isStableEquivalence f T a d
  let : IsIso ((stableHomotopyFunctor d).map
      (homotopyFiberLift ((boundedFlatCoefficientSupportedAmbientBassTelescopeFullOpen f T).app a)
        ((boundedFlatCoefficientSupportedFiberBassTelescopeForget f T).app a)
        ((boundedFlatCoefficientSupportedFiberBassTelescopeFullOpenNull f T).homotopy a))) :=
    boundedFlatCoefficientSupportedFiberBassTelescopeFullOpenFiberMap_isStableEquivalence f T a d
  rw [boundedFlatCoefficientAuxiliaryLocalizationConnecting_eq_fiberLift]
  exact stableFiberLiftConnecting_naturality
    ((boundedFlatCoefficientSupportedFiberForgetPrespectrumTransformation f T).app a)
    ((boundedFlatCoefficientSupportedAmbientOpenPrespectrumTransformation f T).app a)
    ((boundedFlatCoefficientSupportedFiberBassTelescopeForget f T).app a)
    ((boundedFlatCoefficientSupportedAmbientBassTelescopeFullOpen f T).app a)
    ((boundedFlatCoefficientSupportedFiberOpenDiagramNull f T).homotopy a)
    ((boundedFlatCoefficientSupportedFiberBassTelescopeFullOpenNull f T).homotopy a)
    ((boundedFlatCoefficientSupportedFiberBassTelescopeInclusion f T 0).app a)
    ((boundedFlatCoefficientSupportedAmbientBassTelescopeInclusion T 0).app a)
    ((boundedFlatCoefficientSupportedOpenBassTelescopeInclusion f T 0).app a ≫
      (boundedFlatCoefficientSupportedOpenBassTelescopeRestriction f T).app a)
    (boundedFlatCoefficientAuxiliaryInitialTelescope_forget f T a)
    (boundedFlatCoefficientAuxiliaryInitialTelescope_fullOpen f T a)
    (boundedFlatCoefficientAuxiliaryInitialTelescope_fullOpenNull f T a) d

end Quillen.PerfectComplexes
