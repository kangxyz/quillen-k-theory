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

/-! The actual native auxiliary K1 boundary retains its original K0 endpoint and sign. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Quillen.PerfectComplexes
open Quillen.Waldhausen Quillen.Waldhausen.Fibration Quillen.Waldhausen.IteratedS
open Quillen.LoopPrespectrum AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace QuillenTest.AuxiliaryNativeConnecting
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] (T : Q.left.Opens)

/-- K1 enters the original native acyclic K0 with its unchanged single sign. -/
theorem native_auxiliary_Kone_boundary_Kzero (a : Under R)
    (x : (boundedFlatCoefficientSupportedOpenModel f T a).waldhausen.K (0 + 1)) :
    let := boundedFlatCoefficientAuxiliaryInitialFiberLift_isStableEquivalence f T a ((0 : ℕ) : ℤ)
    (stableHomotopyFunctor ((0 : ℕ) : ℤ)).map
        (prespectrumMap (auxiliaryNativeFiberAcyclicModelMap f T a))
        (stableFiberLiftConnecting
          ((boundedFlatCoefficientSupportedFiberForgetPrespectrumTransformation f T).app a)
          ((boundedFlatCoefficientSupportedAmbientOpenPrespectrumTransformation f T).app a)
          ((boundedFlatCoefficientSupportedFiberOpenDiagramNull f T).homotopy a) ((0 : ℕ) : ℤ)
          (eqToHom (congrArg (stableHomotopyGroup
            ((boundedFlatCoefficientSupportedOpenPrespectrumFunctor f T).obj a))
              (show ((0 + 1 : ℕ) : ℤ) = ((0 : ℕ) : ℤ) + 1 from rfl))
            (modelKStableEquiv (boundedFlatCoefficientSupportedOpenModel f T a) (0 + 1)
              (Additive.ofMul x)))) =
      -(originalKStableEquiv (acyclicStructure (boundedFlatCoefficientSupportedOpenNested f T a)) 0
        (Additive.ofMul (changeWeakConnectingHom (boundedFlatCoefficientSupportedOpenNested f T a)
          (boundedFlatCoefficientSupportedOpen_canonicalFiberMap_isWeakHomotopyEquivalence f T a) 0
          x))) := by
  exact boundedFlatCoefficientAuxiliaryInitialConnecting_native_sign f T a 0 rfl x

end QuillenTest.AuxiliaryNativeConnecting
