/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportEvaluationNull
public import Quillen.Topology.Prespectrum.FiberLiftConnecting
public import Quillen.Topology.Prespectrum.ConeDescStableEquivalence

/-!
# The original initial coefficient boundary under geometric evaluation

The literal initial supported inclusion, coarse arrow and prescribed whole null
have a genuine stable fiber lift. Their intrinsic connecting map is natural for
the original evaluation square in every signed degree.
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
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q) [IsOpenImmersion f.left]

/-- The original initial localization null gives a genuine stable fiber equivalence. -/
theorem boundedFlatCoefficientInitialFiberLift_isStableEquivalence (a : Under R) :
    IsStableEquivalence (homotopyFiberLift
      ((boundedFlatCoefficientAmbientOpenPrespectrumTransformation f).app a)
      ((boundedFlatCoefficientSupportedForgetPrespectrumTransformation f).app a)
      ((boundedFlatCoefficientSupportedOpenDiagramNull f).homotopy a)) :=
  homotopyFiberLift_isStableEquivalence_of_coneDesc _ _ _
    (prespectrum_mappingConeFiberComparison_isStableEquivalence
      ((boundedFlatCoefficientSupportedForgetPrespectrumTransformation f).app a))
    (boundedFlatCoefficientSupportedOpenConeComparison_isStableEquivalence f a)

/-- The actual geometric acyclic lift is invertible in every degree at its literal endpoint. -/
theorem boundedFlatCoefficientGeometricFiberLift_isStableEquivalence (a : Under R) :
    IsStableEquivalence (homotopyFiberLift
      (changeWeakPrespectrumMap (boundedFlatPerfectOpenNested (schemeMap f a)))
      (acyclicInclusionPrespectrumMap (boundedFlatPerfectOpenNested (schemeMap f a)))
      (acyclicPrespectrumNullhomotopy (boundedFlatPerfectOpenNested (schemeMap f a)))) :=
  canonicalFiberPrespectrumMap_isStableEquivalence_of_weak _
    (boundedFlatPerfectOpen_canonicalFiberMap_isWeakHomotopyEquivalence (schemeMap f a))

/-- The original evaluation square preserves the intrinsic initial signed boundary. -/
theorem boundedFlatCoefficientInitialConnecting_evaluation (a : Under R) (d : ℤ) :
    let := boundedFlatCoefficientInitialFiberLift_isStableEquivalence f a d
    let := boundedFlatCoefficientGeometricFiberLift_isStableEquivalence f a d
    stableFiberLiftConnecting
        ((boundedFlatCoefficientSupportedForgetPrespectrumTransformation f).app a)
        ((boundedFlatCoefficientAmbientOpenPrespectrumTransformation f).app a)
        ((boundedFlatCoefficientSupportedOpenDiagramNull f).homotopy a) d ≫
        (stableHomotopyFunctor d).map (prespectrumMap (supportAcyclicEvaluationModelMap f a)) =
      (stableHomotopyFunctor (d + 1)).map (prespectrumMap (coarseOriginalEvaluationModelMap f a)) ≫
        stableFiberLiftConnecting
          (acyclicInclusionPrespectrumMap (boundedFlatPerfectOpenNested (schemeMap f a)))
          (changeWeakPrespectrumMap (boundedFlatPerfectOpenNested (schemeMap f a)))
          (acyclicPrespectrumNullhomotopy (boundedFlatPerfectOpenNested (schemeMap f a))) d := by
  let := boundedFlatCoefficientInitialFiberLift_isStableEquivalence f a d
  let := boundedFlatCoefficientGeometricFiberLift_isStableEquivalence f a d
  apply stableFiberLiftConnecting_naturality
    ((boundedFlatCoefficientSupportedForgetPrespectrumTransformation f).app a)
    ((boundedFlatCoefficientAmbientOpenPrespectrumTransformation f).app a)
    (acyclicInclusionPrespectrumMap (boundedFlatPerfectOpenNested (schemeMap f a)))
    (changeWeakPrespectrumMap (boundedFlatPerfectOpenNested (schemeMap f a)))
    ((boundedFlatCoefficientSupportedOpenDiagramNull f).homotopy a)
    (acyclicPrespectrumNullhomotopy (boundedFlatPerfectOpenNested (schemeMap f a)))
    (prespectrumMap (supportAcyclicEvaluationModelMap f a))
    (prespectrumMap (ambientOriginalEvaluationModelMap a))
    (prespectrumMap (coarseOriginalEvaluationModelMap f a))
  · exact (Arrow.w (supportOriginalEvaluationSquare f a)).symm
  · exact ((prespectrumFunctor.map_comp _ _).symm.trans
      ((congrArg prespectrumFunctor.map (coarseOriginalEvaluationModelMap_changeWeak f a)).trans
        (prespectrumFunctor.map_comp _ _))).symm
  · exact supportOriginalEvaluationNull f a

end Quillen.PerfectComplexes
