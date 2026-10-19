/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluation
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalEvaluationStableComparison
public import Quillen.Topology.Prespectrum.StrictSquareTopology
public import Quillen.Waldhausen.SConstruction.Iterated.PointHEP
public import Quillen.Topology.Prespectrum.PushoutHomotopySquareEquivalence
public import Quillen.Topology.Prespectrum.ConeSquareLevelWeakEquivalence
public import Quillen.Topology.Prespectrum.ParameterLoopingWeakEquivalence

/-!
# Weak and stable equivalence of the actual one-step global Bass evaluation

Original normalized evaluation is a complete weak equivalence at every level. The genuine
point HEP of the original spectra and spans makes the actual overlap-descended span, cone
and parameter-loop maps complete weak equivalences. No geometric excision premise is added.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u
namespace Quillen.PerfectComplexes.GlobalBassEvaluation
open GlobalSectionChangeIndex

/-- The original global normalized evaluation is completely weak at every spectrum level. -/
theorem evaluation_level_isWeakHomotopyEquivalence (X : Scheme.{u}) (n : ℕ) :
    IsWeakHomotopyEquivalence ((evaluation X).map n) :=
  ExactModelEquivalence.level_isWeakHomotopyEquivalence (evaluationModelEquivalence (op X))
    (evaluationModel (op X)).exact (evaluationSmallEquivalence_inverse_exact (op X))
    (evaluationModel (op X)).zero n

/-- The actual strict section span retains its original well-based point. -/
theorem sectionSpan_point_homotopyExtensionProperty (X : Scheme.{u}) (n : ℕ) :
    Quillen.homotopyExtensionProperty (TopCat.ofHom (ContinuousMap.const PUnit.{u+2}
      ((StrictSquare.span (sectionSquare X)).point n))) :=
  StrictSquare.span_point_homotopyExtensionProperty _ n
    (prespectrum_point_homotopyExtensionProperty (globalModel.obj (op X)) n)
    (prespectrum_point_homotopyExtensionProperty (globalModel.obj (op (polynomial.obj X))) n)
    (prespectrum_point_homotopyExtensionProperty (globalModel.obj (op (polynomial.obj X))) n)

/-- The actual raw polynomial span has genuine point HEP at every level, including zero. -/
theorem rawSpan_point_homotopyExtensionProperty (X : Scheme.{u}) (n : ℕ) :
    Quillen.homotopyExtensionProperty (TopCat.ofHom (ContinuousMap.const PUnit.{u+2}
      ((GlobalRawBass.span X).point n))) :=
  HomotopyPushout.point_homotopyExtensionProperty _ _ n
    (originalPrespectrum_point_homotopyExtensionProperty (boundedFlatPerfectWaldhausen X) n)
    (originalPrespectrum_point_homotopyExtensionProperty
      (boundedFlatPerfectWaldhausen (polynomial.obj X)) n)
    (originalPrespectrum_point_homotopyExtensionProperty
      (boundedFlatPerfectWaldhausen (polynomial.obj X)) n)

/-- The unchanged whole-track polynomial-span evaluation is completely weak at every level. -/
theorem spanEvaluation_level_isWeakHomotopyEquivalence (X : Scheme.{u}) (n : ℕ) :
    IsWeakHomotopyEquivalence ((spanEvaluation X).map n) :=
  HomotopyPushout.mapOfHomotopies_level_isWeakHomotopyEquivalence
    (sectionMap (projection.app X)) (sectionMap (projection.app X))
    (boundedFlatPerfectPrespectrumMap (projection.app X))
    (boundedFlatPerfectPrespectrumMap (projection.app X))
    (evaluation X) (evaluation (polynomial.obj X)) (evaluation (polynomial.obj X))
    (evaluationComparison (projection.app X)) (evaluationComparison (projection.app X)) n
    (prespectrum_point_homotopyExtensionProperty (globalModel.obj (op X)) n)
    (prespectrum_point_homotopyExtensionProperty (globalModel.obj (op (polynomial.obj X))) n)
    (prespectrum_point_homotopyExtensionProperty (globalModel.obj (op (polynomial.obj X))) n)
    (originalPrespectrum_point_homotopyExtensionProperty (boundedFlatPerfectWaldhausen X) n)
    (originalPrespectrum_point_homotopyExtensionProperty
      (boundedFlatPerfectWaldhausen (polynomial.obj X)) n)
    (originalPrespectrum_point_homotopyExtensionProperty
      (boundedFlatPerfectWaldhausen (polynomial.obj X)) n)
    (evaluation_level_isWeakHomotopyEquivalence X n)
    (evaluation_level_isWeakHomotopyEquivalence (polynomial.obj X) n)
    (evaluation_level_isWeakHomotopyEquivalence (polynomial.obj X) n)

/-- The literal cone evaluation with the proved original overlap is completely weak. -/
theorem coneEvaluation_level_isWeakHomotopyEquivalence (X : Scheme.{u}) (n : ℕ) :
    IsWeakHomotopyEquivalence ((coneEvaluation X).map n) :=
  mappingConeSquareMap_level_isWeakHomotopyEquivalence
    (StrictSquare.comparison (sectionSquare X)) (GlobalRawBass.comparison X)
    (spanEvaluation X) (evaluation (laurent.obj X)) (comparisonHomotopy X) n
    (sectionSpan_point_homotopyExtensionProperty X n)
    (prespectrum_point_homotopyExtensionProperty (globalModel.obj (op (laurent.obj X))) n)
    (rawSpan_point_homotopyExtensionProperty X n)
    (originalPrespectrum_point_homotopyExtensionProperty
      (boundedFlatPerfectWaldhausen (laurent.obj X)) n)
    (spanEvaluation_level_isWeakHomotopyEquivalence X n)
    (evaluation_level_isWeakHomotopyEquivalence (laurent.obj X) n)

/-- Parameter looping preserves every component of the actual cone evaluation, also at zero. -/
theorem stepEvaluation_level_isWeakHomotopyEquivalence (X : Scheme.{u}) (n : ℕ) :
    IsWeakHomotopyEquivalence ((stepEvaluation X).map n) :=
  basedLoopMap_isWeakHomotopyEquivalence ((coneEvaluation X).map n)
    ((coneEvaluation X).map_point n) (coneEvaluation_level_isWeakHomotopyEquivalence X n)

/-- The actual strict-section to raw Bass step evaluation is stable in every signed degree. -/
theorem stepEvaluation_isStableEquivalence (X : Scheme.{u}) :
    IsStableEquivalence (stepEvaluation X) :=
  isStableEquivalence_of_levelwise _ (stepEvaluation_level_isWeakHomotopyEquivalence X)

end Quillen.PerfectComplexes.GlobalBassEvaluation
