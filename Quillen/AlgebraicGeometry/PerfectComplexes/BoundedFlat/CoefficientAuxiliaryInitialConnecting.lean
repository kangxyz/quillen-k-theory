/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientAuxiliaryEvaluationNull
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportedNativeFibration
public import Quillen.Topology.Prespectrum.FiberLiftConnecting
public import Quillen.Topology.Prespectrum.ConeDescStableEquivalence

/-!
# The original initial auxiliary boundary under native acyclic conversion

The literal initial intersection-support inclusion, coarse arrow and prescribed whole null
have a genuine stable fiber lift. Their intrinsic connecting map is natural for
the original native conversion square in every signed degree.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.Waldhausen Quillen.Waldhausen.Fibration Quillen.Waldhausen.IteratedS
open Quillen.LoopPrespectrum AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] (T : Q.left.Opens)

/-- The original initial localization null gives a genuine stable fiber equivalence. -/
theorem boundedFlatCoefficientAuxiliaryInitialFiberLift_isStableEquivalence (a : Under R) :
    IsStableEquivalence (homotopyFiberLift
      ((boundedFlatCoefficientSupportedAmbientOpenPrespectrumTransformation f T).app a)
      ((boundedFlatCoefficientSupportedFiberForgetPrespectrumTransformation f T).app a)
      ((boundedFlatCoefficientSupportedFiberOpenDiagramNull f T).homotopy a)) :=
  homotopyFiberLift_isStableEquivalence_of_coneDesc _ _ _
    (prespectrum_mappingConeFiberComparison_isStableEquivalence
      ((boundedFlatCoefficientSupportedFiberForgetPrespectrumTransformation f T).app a))
    (boundedFlatCoefficientSupportedFiberOpenConeComparison_isStableEquivalence f T a)

/-- The actual native acyclic lift is invertible in every degree at its literal endpoint. -/
theorem boundedFlatCoefficientAuxiliaryNativeFiberLift_isStableEquivalence (a : Under R) :
    IsStableEquivalence (homotopyFiberLift
      (changeWeakPrespectrumMap (boundedFlatCoefficientSupportedOpenNested f T a))
      (acyclicInclusionPrespectrumMap (boundedFlatCoefficientSupportedOpenNested f T a))
      (acyclicPrespectrumNullhomotopy (boundedFlatCoefficientSupportedOpenNested f T a))) :=
  canonicalFiberPrespectrumMap_isStableEquivalence_of_weak _
    (boundedFlatCoefficientSupportedOpen_canonicalFiberMap_isWeakHomotopyEquivalence f T a)

/-- The original native conversion square preserves the intrinsic initial signed boundary. -/
theorem boundedFlatCoefficientAuxiliaryInitialConnecting_native (a : Under R) (d : ℤ) :
    let := boundedFlatCoefficientAuxiliaryInitialFiberLift_isStableEquivalence f T a d
    let := boundedFlatCoefficientAuxiliaryNativeFiberLift_isStableEquivalence f T a d
    stableFiberLiftConnecting
        ((boundedFlatCoefficientSupportedFiberForgetPrespectrumTransformation f T).app a)
        ((boundedFlatCoefficientSupportedAmbientOpenPrespectrumTransformation f T).app a)
        ((boundedFlatCoefficientSupportedFiberOpenDiagramNull f T).homotopy a) d ≫
        (stableHomotopyFunctor d).map (prespectrumMap (auxiliaryNativeFiberAcyclicModelMap f T a)) =
      (stableHomotopyFunctor (d + 1)).map (prespectrumMap (auxiliaryNativeCoarseModelMap f T a)) ≫
        stableFiberLiftConnecting
          (acyclicInclusionPrespectrumMap (boundedFlatCoefficientSupportedOpenNested f T a))
          (changeWeakPrespectrumMap (boundedFlatCoefficientSupportedOpenNested f T a))
          (acyclicPrespectrumNullhomotopy (boundedFlatCoefficientSupportedOpenNested f T a)) d := by
  let := boundedFlatCoefficientAuxiliaryInitialFiberLift_isStableEquivalence f T a d
  let := boundedFlatCoefficientAuxiliaryNativeFiberLift_isStableEquivalence f T a d
  apply stableFiberLiftConnecting_naturality
    ((boundedFlatCoefficientSupportedFiberForgetPrespectrumTransformation f T).app a)
    ((boundedFlatCoefficientSupportedAmbientOpenPrespectrumTransformation f T).app a)
    (acyclicInclusionPrespectrumMap (boundedFlatCoefficientSupportedOpenNested f T a))
    (changeWeakPrespectrumMap (boundedFlatCoefficientSupportedOpenNested f T a))
    ((boundedFlatCoefficientSupportedFiberOpenDiagramNull f T).homotopy a)
    (acyclicPrespectrumNullhomotopy (boundedFlatCoefficientSupportedOpenNested f T a))
    (prespectrumMap (auxiliaryNativeFiberAcyclicModelMap f T a))
    (prespectrumMap (auxiliaryNativeAmbientModelMap T a))
    (prespectrumMap (auxiliaryNativeCoarseModelMap f T a))
  · exact (Arrow.w (auxiliaryNativeFiberEvaluationSquare f T a)).symm
  · exact ((prespectrumFunctor.map_comp _ _).symm.trans
      ((congrArg prespectrumFunctor.map (auxiliaryNativeCoarseModelMap_changeWeak f T a)).trans
        (prespectrumFunctor.map_comp _ _))).symm
  · exact auxiliaryNativeFiberEvaluationNull f T a

end Quillen.PerfectComplexes
