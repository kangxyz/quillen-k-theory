/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedSectionOpenConeComparison

/-!
# Consumers of the original supported-section cone comparison

These consumers retain the inherited zero, literal inclusion, full null path, independent
structure time, unchanged target face and signed boundary. The endpoint is the original
relative-open coarse section model.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
universe u
namespace QuillenTest.SupportedSectionOpenConeComparison

open Quillen
open PerfectComplexes Waldhausen Waldhausen.Fibration Waldhausen.IteratedS
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- Evaluation followed by the acyclic inclusion is the original supported section evaluation. -/
theorem original_acyclic_inclusion (s : BoundedFlatAffineSupportedSections j) :
    ((boundedFlatAffineSupportedSectionAcyclicEvaluation j).obj s).obj =
      (boundedFlatAffineOriginalEvaluation R).obj s.obj :=
  congrArg (fun F => F.obj s) (boundedFlatAffineSupportedSectionAcyclicEvaluation_inclusion j)

/-- The inherited zero is retained without identifying independently chosen supported zeros. -/
theorem original_inherited_zero :
    (boundedFlatAffineSupportedSectionAcyclicEvaluation j).obj
        (boundedFlatAffineSupportedSectionWaldhausen j).zero =
      (acyclicStructure (boundedFlatPerfectOpenNested j)).zero :=
  boundedFlatAffineSupportedSectionAcyclicEvaluation_zero j

/-- Every value of the original reversed null cylinder agrees under actual evaluation. -/
theorem original_whole_null_evaluation (n : ℕ) (s : unitInterval)
    (x : (prespectrum (boundedFlatAffineSupportedSectionModel j)).space n) :
    (boundedFlatAffineSectionOpenEvaluationPrespectrumMap j).map n
        ((boundedFlatAffineSupportedSectionOpenNullHomotopy j).level n (s, x)) =
      (acyclicPrespectrumNullhomotopy (boundedFlatPerfectOpenNested j)).level n
        (s, (boundedFlatAffineSupportedSectionAcyclicPrespectrumMap j).map n x) :=
  boundedFlatAffineSupportedSectionOpenNullHomotopy_evaluation j n s x

/-- Structure and null-homotopy parameters remain independent in the original comparison. -/
theorem original_independent_structure_and_null (n : ℕ) (s t : unitInterval)
    (x : (prespectrum (boundedFlatAffineSupportedSectionModel j)).space n) :
    (boundedFlatAffineSectionOpenEvaluationPrespectrumMap j).map (n + 1)
        ((boundedFlatAffineSupportedSectionOpenNullHomotopy j).level (n + 1)
          (s, (prespectrum (boundedFlatAffineSupportedSectionModel j)).structureMap n x t)) =
      (acyclicPrespectrumNullhomotopy (boundedFlatPerfectOpenNested j)).level (n + 1)
        (s, (originalPrespectrum (acyclicStructure (boundedFlatPerfectOpenNested j))).structureMap n
          ((boundedFlatAffineSupportedSectionAcyclicPrespectrumMap j).map n x) t) := by
  exact (boundedFlatAffineSupportedSectionOpenNullHomotopy_evaluation j (n + 1) s
    ((prespectrum (boundedFlatAffineSupportedSectionModel j)).structureMap n x t)).trans
      (congrArg (fun y =>
        (acyclicPrespectrumNullhomotopy (boundedFlatPerfectOpenNested j)).level (n + 1) (s, y))
        (congrArg (fun γ => γ t)
          ((boundedFlatAffineSupportedSectionAcyclicPrespectrumMap j).comm n x)))

/-- The cone target face is the unchanged original fine-to-relative-open section map. -/
theorem original_cone_target_face :
    mappingConeInclusion (boundedFlatAffineSupportedSectionForgetPrespectrumMap j) ≫
        boundedFlatAffineSupportedSectionOpenConeMap j =
      boundedFlatAffineSectionOpenPrespectrumMap j :=
  boundedFlatAffineSupportedSectionOpenConeMap_inclusion j

/-- The cone evaluation square uses the original actual inclusion square and descent. -/
theorem original_cone_evaluation_square :
    mappingConeMap (boundedFlatAffineSupportedSectionOpenInclusionSquare j) ≫
        boundedFlatPerfectOpenConeComparison j =
      boundedFlatAffineSupportedSectionOpenConeMap j ≫
        boundedFlatAffineSectionOpenEvaluationPrespectrumMap j :=
  boundedFlatAffineSupportedSectionOpenConeMap_evaluation j

/-- The unchanged original cone comparison induces an isomorphism in each signed degree. -/
theorem original_signed_isomorphism (d : ℤ) :
    IsIso ((stableHomotopyFunctor d).map (boundedFlatAffineSupportedSectionOpenConeMap j)) :=
  boundedFlatAffineSupportedSectionOpenConeMap_isStableEquivalence j d

/-- Every original negative relative-open class has an actual cone class lifting it. -/
theorem original_negative_class_lift (n : ℕ)
    (y : stableHomotopyGroup (prespectrum (boundedFlatAffineSectionOpenModel j))
      (-(n : ℤ) - 1)) :
    ∃ x, (stableHomotopyFunctor (-(n : ℤ) - 1)).map
      (boundedFlatAffineSupportedSectionOpenConeMap j) x = y := by
  let := boundedFlatAffineSupportedSectionOpenConeMap_isStableEquivalence j (-(n : ℤ) - 1)
  exact (ConcreteCategory.bijective_of_isIso ((stableHomotopyFunctor (-(n : ℤ) - 1)).map
    (boundedFlatAffineSupportedSectionOpenConeMap j))).surjective y

/-- The signed boundary retains the original source map and its entire specified fiber path. -/
theorem original_signed_boundary (d : ℤ) :
    (stableHomotopyFunctor (d + 1)).map (boundedFlatAffineSupportedSectionOpenConeMap j) ≫
        stableFiberConnecting (boundedFlatAffineSectionOpenPrespectrumMap j) d =
      stableMappingConeConnecting (boundedFlatAffineSupportedSectionForgetPrespectrumMap j)
          (prespectrum_mappingConeFiberComparison_isStableEquivalence
            (boundedFlatAffineSupportedSectionForgetPrespectrumMap j)) d ≫
        (stableHomotopyFunctor d).map
          (homotopyFiberLift (boundedFlatAffineSectionOpenPrespectrumMap j)
            (boundedFlatAffineSupportedSectionForgetPrespectrumMap j)
            (boundedFlatAffineSupportedSectionOpenNullHomotopy j)) :=
  boundedFlatAffineSupportedSectionOpenConeMap_connecting j d

end QuillenTest.SupportedSectionOpenConeComparison
