/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Polynomial.Laurent.UnderSquare
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSectionEvaluationSourceLeg
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSectionEvaluationBassSeed
public import Quillen.Waldhausen.SConstruction.Iterated.ExactModelEquivalence
public import Quillen.Waldhausen.SConstruction.Iterated.PointHEP
public import Quillen.Topology.Prespectrum.PushoutHomotopySquareEquivalence
public import Quillen.Topology.Prespectrum.StrictSquareTopology

/-!
# Levelwise equivalence and literal point topology of original native evaluation

The common-universe evaluation equivalence is changed along its actual normalization
isomorphism. Its forward functor is therefore literally the original rebased evaluation
Model map, and its inverse remains the original exact lifted inverse. The existing exact-model
construction supplies an actual homotopy inverse at every level, including zero.

The unchanged fine-to-raw polynomial-span map retains both original evaluation tracks.
Genuine point HEP of its six native Models and the three levelwise evaluation equivalences
prove that this actual span map is weak at every level. The original fine and raw spans,
cones and parameter loops have T1 separation and HEP at their literal chosen points.
No compactness, flatness or open-immersion condition is needed for these bounded-flat maps.
Cone descent and comparison of the original source nulls remain separate obligations.
-/
@[expose] public section

open Quillen.Waldhausen


open CommRingCat.PolynomialLaurent

noncomputable section
open CategoryTheory AlgebraicGeometry Opposite Quillen.LoopPrespectrum
open Quillen.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}}

/-- The actual normalized evaluation is the forward functor of this lifted equivalence. -/
def boundedFlatCoefficientSectionEvaluationEquivalence (i : Index R) :
    BoundedFlatCoefficientSections i ≌ SmallModel (BoundedFlatPerfect (space i)) :=
  (boundedFlatCoefficientSectionSmallEquivalence i).changeFunctor
    (boundedFlatCoefficientSectionEvaluationNormalizationIso i)

/-- Normalization changes the equivalence to the original evaluation functor literally. -/
theorem boundedFlatCoefficientSectionEvaluationEquivalence_functor (i : Index R) :
    (boundedFlatCoefficientSectionEvaluationEquivalence i).functor =
      (boundedFlatCoefficientSectionEvaluationModelMap i).functor := rfl

/-- The exact-model forward map is precisely the original evaluation Model map. -/
theorem boundedFlatCoefficientSectionEvaluationEquivalence_forward (i : Index R) :
    ExactModelEquivalence.forward
      (V := boundedFlatCoefficientSectionModel i)
      (W := modelOf (boundedFlatPerfectWaldhausen (space i)))
      (boundedFlatCoefficientSectionEvaluationEquivalence i)
      (boundedFlatCoefficientSectionEvaluationModelMap i).exact
      (boundedFlatCoefficientSectionEvaluationModelMap i).zero =
        boundedFlatCoefficientSectionEvaluationModelMap i := rfl

/-- The original normalized evaluation has an actual homotopy inverse at every level. -/
def boundedFlatCoefficientSectionEvaluationLevelHomotopyEquiv (i : Index R) (n : ℕ) :
    ContinuousMap.HomotopyEquiv
      (((boundedFlatCoefficientSectionPrespectrumFunctor R).obj i).space n)
      ((originalPrespectrum (boundedFlatPerfectWaldhausen (space i))).space n) :=
  ExactModelEquivalence.levelHomotopyEquiv
    (V := boundedFlatCoefficientSectionModel i)
    (W := modelOf (boundedFlatPerfectWaldhausen (space i)))
    (boundedFlatCoefficientSectionEvaluationEquivalence i)
    (boundedFlatCoefficientSectionEvaluationModelMap i).exact
    (boundedFlatCoefficientSectionSmallEquivalence_inverse_exact i)
    (boundedFlatCoefficientSectionEvaluationModelMap i).zero n

/-- The homotopy equivalence retains the unchanged evaluation as its actual forward map. -/
theorem boundedFlatCoefficientSectionEvaluationLevelHomotopyEquiv_toFun
    (i : Index R) (n : ℕ) :
    (boundedFlatCoefficientSectionEvaluationLevelHomotopyEquiv i n).toFun =
      (boundedFlatCoefficientSectionEvaluationPrespectrumMap i).map n := rfl

/-- Original native evaluation is completely weak at every level, including level zero. -/
theorem boundedFlatCoefficientSectionEvaluation_level_isWeakHomotopyEquivalence
    (i : Index R) (n : ℕ) :
    IsWeakHomotopyEquivalence
      ((boundedFlatCoefficientSectionEvaluationPrespectrumMap i).map n) :=
  ExactModelEquivalence.level_isWeakHomotopyEquivalence
    (V := boundedFlatCoefficientSectionModel i)
    (W := modelOf (boundedFlatPerfectWaldhausen (space i)))
    (boundedFlatCoefficientSectionEvaluationEquivalence i)
    (boundedFlatCoefficientSectionEvaluationModelMap i).exact
    (boundedFlatCoefficientSectionSmallEquivalence_inverse_exact i)
    (boundedFlatCoefficientSectionEvaluationModelMap i).zero n

/-- Each original joint native Model is well based at every chosen point. -/
theorem boundedFlatCoefficientSectionPrespectrum_point_homotopyExtensionProperty
    (i : Index R) (n : ℕ) :
    Quillen.homotopyExtensionProperty (TopCat.ofHom (ContinuousMap.const PUnit.{u + 2}
      (((boundedFlatCoefficientSectionPrespectrumFunctor R).obj i).point n))) :=
  prespectrum_point_homotopyExtensionProperty (boundedFlatCoefficientSectionModel i) n

/-- The original joint native realization, including its degree-zero loop, is T1. -/
instance boundedFlatCoefficientSectionPrespectrumSpaceT1Space (i : Index R) (n : ℕ) :
    T1Space (((boundedFlatCoefficientSectionPrespectrumFunctor R).obj i).space n) :=
  prespectrumSpaceT1Space (boundedFlatCoefficientSectionModel i) n

variable {P Q : Over (Spec R)} (f : P ⟶ Q)

/-- The actual fine-to-raw span evaluation with both original tracks is levelwise weak. -/
theorem boundedFlatCoefficientFullOpenBassSpanEvaluation_level_isWeakHomotopyEquivalence
    (a : Under R) (n : ℕ) :
    IsWeakHomotopyEquivalence
      ((boundedFlatCoefficientFullOpenBassSpanEvaluation f a).map n) :=
  HomotopyPushout.mapOfHomotopies_level_isWeakHomotopyEquivalence
    ((boundedFlatCoefficientFullOpenPrespectrumFunctor f).map
      ((polynomialUnderCoefficient R).app a))
    ((boundedFlatCoefficientFullOpenPrespectrumFunctor f).map
      ((polynomialUnderCoefficient R).app a))
    (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
    (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
    (boundedFlatCoefficientSectionEvaluationPrespectrumMap (op P, a))
    (boundedFlatCoefficientSectionEvaluationPrespectrumMap
      (op P, (polynomialUnderFunctor R).obj a))
    (boundedFlatCoefficientSectionEvaluationPrespectrumMap
      (op P, (polynomialUnderFunctor R).obj a))
    (boundedFlatCoefficientSectionEvaluationHomotopy
      (i := (op P, a)) (k := (op P, (polynomialUnderFunctor R).obj a))
      (𝟙 (op P), (polynomialUnderCoefficient R).app a))
    (boundedFlatCoefficientSectionEvaluationHomotopy
      (i := (op P, a)) (k := (op P, (polynomialUnderFunctor R).obj a))
      (𝟙 (op P), (polynomialUnderCoefficient R).app a)) n
    (boundedFlatCoefficientSectionPrespectrum_point_homotopyExtensionProperty (op P, a) n)
    (boundedFlatCoefficientSectionPrespectrum_point_homotopyExtensionProperty
      (op P, (polynomialUnderFunctor R).obj a) n)
    (boundedFlatCoefficientSectionPrespectrum_point_homotopyExtensionProperty
      (op P, (polynomialUnderFunctor R).obj a) n)
    (originalPrespectrum_point_homotopyExtensionProperty
      (boundedFlatPerfectWaldhausen (space (op P, a))) n)
    (originalPrespectrum_point_homotopyExtensionProperty
      (boundedFlatPerfectWaldhausen (space (op P, (polynomialUnderFunctor R).obj a))) n)
    (originalPrespectrum_point_homotopyExtensionProperty
      (boundedFlatPerfectWaldhausen (space (op P, (polynomialUnderFunctor R).obj a))) n)
    (boundedFlatCoefficientSectionEvaluation_level_isWeakHomotopyEquivalence (op P, a) n)
    (boundedFlatCoefficientSectionEvaluation_level_isWeakHomotopyEquivalence
      (op P, (polynomialUnderFunctor R).obj a) n)
    (boundedFlatCoefficientSectionEvaluation_level_isWeakHomotopyEquivalence
      (op P, (polynomialUnderFunctor R).obj a) n)

/-- The unchanged native span evaluation is consequently stable in every signed degree. -/
theorem boundedFlatCoefficientFullOpenBassSpanEvaluation_isStableEquivalence (a : Under R) :
    IsStableEquivalence (boundedFlatCoefficientFullOpenBassSpanEvaluation f a) :=
  isStableEquivalence_of_levelwise _
    (boundedFlatCoefficientFullOpenBassSpanEvaluation_level_isWeakHomotopyEquivalence f a)

/-- The original strict fine span has HEP at its actual chosen point at every level. -/
theorem boundedFlatCoefficientFullOpenBassSpan_point_homotopyExtensionProperty
    (a : Under R) (n : ℕ) :
    Quillen.homotopyExtensionProperty (TopCat.ofHom (ContinuousMap.const PUnit.{u + 2}
      ((StrictSquare.span (boundedFlatCoefficientFullOpenBassSquare f a)).point n))) :=
  StrictSquare.span_point_homotopyExtensionProperty _ n
    (boundedFlatCoefficientSectionPrespectrum_point_homotopyExtensionProperty (op P, a) n)
    (boundedFlatCoefficientSectionPrespectrum_point_homotopyExtensionProperty
      (op P, (polynomialUnderFunctor R).obj a) n)
    (boundedFlatCoefficientSectionPrespectrum_point_homotopyExtensionProperty
      (op P, (polynomialUnderFunctor R).obj a) n)

/-- The original raw native two-chart span has genuine point HEP, including level zero. -/
theorem boundedFlatCoefficientBassSpan_point_homotopyExtensionProperty
    (P : Over (Spec R)) (a : Under R) (n : ℕ) :
    Quillen.homotopyExtensionProperty (TopCat.ofHom (ContinuousMap.const PUnit.{u + 2}
      ((HomotopyPushout.prespectrum
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))).point n))) :=
  HomotopyPushout.point_homotopyExtensionProperty _ _ n
    (originalPrespectrum_point_homotopyExtensionProperty
      (boundedFlatPerfectWaldhausen (space (op P, a))) n)
    (originalPrespectrum_point_homotopyExtensionProperty
      (boundedFlatPerfectWaldhausen (space (op P, (polynomialUnderFunctor R).obj a))) n)
    (originalPrespectrum_point_homotopyExtensionProperty
      (boundedFlatPerfectWaldhausen (space (op P, (polynomialUnderFunctor R).obj a))) n)

/-- The original strict fine span retains the actual quotient's T1 separation. -/
instance boundedFlatCoefficientFullOpenBassSpanSpaceT1Space (a : Under R) (n : ℕ) :
    T1Space ((StrictSquare.span (boundedFlatCoefficientFullOpenBassSquare f a)).space n) :=
  @StrictSquare.spanSpaceT1Space _ _
    (prespectrumSpaceT1Space (boundedFlatCoefficientSectionModel (op P, a)) n)
    (prespectrumSpaceT1Space
      (boundedFlatCoefficientSectionModel (op P, (polynomialUnderFunctor R).obj a)) n)
    (prespectrumSpaceT1Space
      (boundedFlatCoefficientSectionModel (op P, (polynomialUnderFunctor R).obj a)) n)

/-- The unchanged raw native span has T1 separation in its original topology. -/
instance boundedFlatCoefficientBassSpanSpaceT1Space
    (P : Over (Spec R)) (a : Under R) (n : ℕ) :
    T1Space ((HomotopyPushout.prespectrum
      (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
      (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))).space n) := by
  infer_instance

/-- The original fine cone has HEP at its literal point in every degree. -/
theorem boundedFlatCoefficientFullOpenBassCone_point_homotopyExtensionProperty
    (a : Under R) (n : ℕ) :
    Quillen.homotopyExtensionProperty (TopCat.ofHom (ContinuousMap.const PUnit.{u + 2}
      ((boundedFlatCoefficientFullOpenBassCone f a).point n))) :=
  ReducedMappingCone.point_homotopyExtensionProperty _ _ _
    ((StrictSquare.comparison (boundedFlatCoefficientFullOpenBassSquare f a)).map_point n)
    (boundedFlatCoefficientFullOpenBassSpan_point_homotopyExtensionProperty f a n)
    (boundedFlatCoefficientSectionPrespectrum_point_homotopyExtensionProperty
      (op P, (laurentUnderFunctor R).obj a) n)

/-- The unchanged raw native comparison cone is well based at every level. -/
theorem boundedFlatCoefficientBassCone_point_homotopyExtensionProperty
    (P : Over (Spec R)) (a : Under R) (n : ℕ) :
    Quillen.homotopyExtensionProperty (TopCat.ofHom (ContinuousMap.const PUnit.{u + 2}
      ((mappingCone (boundedFlatCoefficientBassSquareComparison P a)).point n))) :=
  ReducedMappingCone.point_homotopyExtensionProperty _ _ _
    ((boundedFlatCoefficientBassSquareComparison P a).map_point n)
    (boundedFlatCoefficientBassSpan_point_homotopyExtensionProperty P a n)
    (originalPrespectrum_point_homotopyExtensionProperty
      (boundedFlatPerfectWaldhausen (space (op P, (laurentUnderFunctor R).obj a))) n)

/-- The actual fine cone's chosen point is closed by T1 separation of its native inputs. -/
instance boundedFlatCoefficientFullOpenBassConeSpaceT1Space (a : Under R) (n : ℕ) :
    T1Space ((boundedFlatCoefficientFullOpenBassCone f a).space n) := by
  let : T1Space ((boundedFlatCoefficientFullOpenBassSquare f a).right.right.space n) :=
    prespectrumSpaceT1Space
      (boundedFlatCoefficientSectionModel (op P, (laurentUnderFunctor R).obj a)) n
  change T1Space ((mappingCone
    (StrictSquare.comparison (boundedFlatCoefficientFullOpenBassSquare f a))).space n)
  infer_instance

/-- The original raw native cone retains T1 separation, with no replacement cone. -/
instance boundedFlatCoefficientBassConeSpaceT1Space
    (P : Over (Spec R)) (a : Under R) (n : ℕ) :
    T1Space ((mappingCone (boundedFlatCoefficientBassSquareComparison P a)).space n) := by
  infer_instance

/-- Closedness and HEP of the original fine cone point give HEP of its actual parameter loop. -/
theorem boundedFlatCoefficientFullOpenBassLoopedCone_point_homotopyExtensionProperty
    (a : Under R) (n : ℕ) :
    Quillen.homotopyExtensionProperty (TopCat.ofHom (ContinuousMap.const PUnit.{u + 2}
      ((strictSquareLoopedConeFunctor.obj
        (boundedFlatCoefficientFullOpenBassSquare f a)).point n))) :=
  parameterLooping_point_homotopyExtensionProperty (boundedFlatCoefficientFullOpenBassCone f a) n
    isClosed_singleton
    (boundedFlatCoefficientFullOpenBassCone_point_homotopyExtensionProperty f a n)

/-- The unchanged raw native one-step parameter loop has HEP at every literal point. -/
theorem boundedFlatCoefficientBassStep_point_homotopyExtensionProperty
    (P : Over (Spec R)) (a : Under R) (n : ℕ) :
    Quillen.homotopyExtensionProperty (TopCat.ofHom (ContinuousMap.const PUnit.{u + 2}
      ((boundedFlatCoefficientBassStep P a).point n))) :=
  parameterLooping_point_homotopyExtensionProperty
    (mappingCone (boundedFlatCoefficientBassSquareComparison P a)) n isClosed_singleton
    (boundedFlatCoefficientBassCone_point_homotopyExtensionProperty P a n)

/-- The actual fine parameter-looped cone has T1 separation at every original level. -/
instance boundedFlatCoefficientFullOpenBassLoopedConeSpaceT1Space (a : Under R) (n : ℕ) :
    T1Space
      ((strictSquareLoopedConeFunctor.obj
        (boundedFlatCoefficientFullOpenBassSquare f a)).space n) := by
  change T1Space ((parameterLooping (boundedFlatCoefficientFullOpenBassCone f a)).space n)
  infer_instance

/-- T1 separation passes to the unchanged raw native one-step parameter loop. -/
instance boundedFlatCoefficientBassStepSpaceT1Space
    (P : Over (Spec R)) (a : Under R) (n : ℕ) :
    T1Space ((boundedFlatCoefficientBassStep P a).space n) := by
  change T1Space ((parameterLooping
    (mappingCone (boundedFlatCoefficientBassSquareComparison P a))).space n)
  infer_instance

end Quillen.PerfectComplexes
