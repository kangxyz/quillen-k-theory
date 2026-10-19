/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientAuxiliaryInitialConnectingSign
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientAuxiliaryInitialTelescopeConnecting

/-! The original intrinsic auxiliary boundary kills the actual initial restriction. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Quillen.PerfectComplexes
open Quillen.Waldhausen Quillen.Waldhausen.Fibration Quillen.Waldhausen.IteratedS
open Quillen.LoopPrespectrum AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace Consumer.AuxiliaryNativeConnecting
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] (T : Q.left.Opens)

/-- Exactness uses the original native restriction and the original specified fiber lift. -/
theorem original_auxiliary_boundary_kills_restriction (a : Under R) (d : ℤ)
    (x : stableHomotopyGroup
      ((boundedFlatCoefficientSupportedAmbientPrespectrumFunctor T).obj a) (d + 1)) :
    let := boundedFlatCoefficientAuxiliaryInitialFiberLift_isStableEquivalence f T a d
    stableFiberLiftConnecting
        ((boundedFlatCoefficientSupportedFiberForgetPrespectrumTransformation f T).app a)
        ((boundedFlatCoefficientSupportedAmbientOpenPrespectrumTransformation f T).app a)
        ((boundedFlatCoefficientSupportedFiberOpenDiagramNull f T).homotopy a) d
        ((stableHomotopyFunctor (d + 1)).map
          ((boundedFlatCoefficientSupportedAmbientOpenPrespectrumTransformation f T).app a) x) =
      0 := by
  let := boundedFlatCoefficientAuxiliaryInitialFiberLift_isStableEquivalence f T a d
  change (inv ((stableHomotopyFunctor d).map
      (homotopyFiberLift
        ((boundedFlatCoefficientSupportedAmbientOpenPrespectrumTransformation f T).app a)
        ((boundedFlatCoefficientSupportedFiberForgetPrespectrumTransformation f T).app a)
        ((boundedFlatCoefficientSupportedFiberOpenDiagramNull f T).homotopy a))))
      (stableFiberConnecting
        ((boundedFlatCoefficientSupportedAmbientOpenPrespectrumTransformation f T).app a) d
        ((stableHomotopyFunctor (d + 1)).map
          ((boundedFlatCoefficientSupportedAmbientOpenPrespectrumTransformation f T).app a) x)) = 0
  rw [(stableFiberConnecting_exact_target
    ((boundedFlatCoefficientSupportedAmbientOpenPrespectrumTransformation f T).app a) d _).mpr
    ⟨x, rfl⟩, map_zero]

end Consumer.AuxiliaryNativeConnecting
