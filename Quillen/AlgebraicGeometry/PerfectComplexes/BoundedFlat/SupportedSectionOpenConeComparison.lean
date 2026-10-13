/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedSectionOpenNullNaturality
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.OpenConeComparison
public import Quillen.Topology.Prespectrum.ConeDescNaturality
public import Quillen.Topology.Prespectrum.ConeStableNaturality

/-!
# The original supported-section cone comparison

The actual supported-section evaluation and inherited-zero inclusion square identify the
original whole null track with the geometric acyclic track. Genuine S-model excision and
both actual evaluation equivalences therefore prove stability of the unchanged section
cone descent. Its target is the relative-open coarse section model; the full-open K₀-image
endpoint remains separate. The signed boundary retains the specified original fiber lift.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
universe u
namespace Quillen.PerfectComplexes
open Waldhausen Waldhausen.Fibration Waldhausen.IteratedS
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- The actual supported evaluation square between the original inclusion arrows. -/
def boundedFlatAffineSupportedSectionOpenInclusionSquare :
    Arrow.mk (boundedFlatAffineSupportedSectionForgetPrespectrumMap j) ⟶
      Arrow.mk (acyclicInclusionPrespectrumMap (boundedFlatPerfectOpenNested j)) :=
  Arrow.homMk (boundedFlatAffineSupportedSectionAcyclicPrespectrumMap j)
    (boundedFlatAffineSectionEvaluationPrespectrumMap R)
    (boundedFlatAffineSupportedSectionAcyclicPrespectrumMap_inclusion j).symm

/-- The original section cone descent commutes with evaluation on both faces and the whole track. -/
theorem boundedFlatAffineSupportedSectionOpenConeMap_evaluation :
    mappingConeMap (boundedFlatAffineSupportedSectionOpenInclusionSquare j) ≫
        boundedFlatPerfectOpenConeComparison j =
      boundedFlatAffineSupportedSectionOpenConeMap j ≫
        boundedFlatAffineSectionOpenEvaluationPrespectrumMap j :=
  mappingConeDesc_naturality (boundedFlatAffineSupportedSectionOpenInclusionSquare j)
    (boundedFlatAffineSectionOpenPrespectrumMap j)
    (changeWeakPrespectrumMap (boundedFlatPerfectOpenNested j))
    (boundedFlatAffineSectionOpenEvaluationPrespectrumMap j)
    (boundedFlatAffineSupportedSectionOpenNullHomotopy j)
    (acyclicPrespectrumNullhomotopy (boundedFlatPerfectOpenNested j))
    (boundedFlatAffineSectionOpenEvaluation_changeWeak j).symm
    (boundedFlatAffineSupportedSectionOpenNullHomotopy_evaluation j)

/-- Original S-model excision and the actual evaluation equivalences prove cone-map stability. -/
theorem boundedFlatAffineSupportedSectionOpenInclusionSquare_cone_isStableEquivalence :
    IsStableEquivalence (mappingConeMap (boundedFlatAffineSupportedSectionOpenInclusionSquare j)) :=
  mappingConeMap_isStableEquivalence_of_excision
    (boundedFlatAffineSupportedSectionOpenInclusionSquare j)
    (prespectrum_mappingConeFiberComparison_isStableEquivalence
      (boundedFlatAffineSupportedSectionForgetPrespectrumMap j))
    (originalPrespectrum_mappingConeFiberComparison_isStableEquivalence _ _ _)
    (boundedFlatAffineSupportedSectionAcyclic_isStableEquivalence j)
    (boundedFlatAffineSectionEvaluation_isStableEquivalence R)

/-- The unchanged supported-section cone descent is an equivalence in every signed stable degree. -/
theorem boundedFlatAffineSupportedSectionOpenConeMap_isStableEquivalence :
    IsStableEquivalence (boundedFlatAffineSupportedSectionOpenConeMap j) := by
  have hc := (boundedFlatAffineSupportedSectionOpenInclusionSquare_cone_isStableEquivalence j).comp
    (boundedFlatPerfectOpenConeComparison_isStableEquivalence j)
  rw [boundedFlatAffineSupportedSectionOpenConeMap_evaluation] at hc
  intro d
  let := boundedFlatAffineSectionOpenEvaluation_isStableEquivalence j d
  have hd := hc d
  rw [Functor.map_comp] at hd
  exact (isIso_comp_right_iff _ _).mp hd

/-- The original signed cone boundary equals the actual relative-open fiber boundary. -/
theorem boundedFlatAffineSupportedSectionOpenConeMap_connecting (d : ℤ) :
    (stableHomotopyFunctor (d + 1)).map (boundedFlatAffineSupportedSectionOpenConeMap j) ≫
        stableFiberConnecting (boundedFlatAffineSectionOpenPrespectrumMap j) d =
      stableMappingConeConnecting (boundedFlatAffineSupportedSectionForgetPrespectrumMap j)
          (prespectrum_mappingConeFiberComparison_isStableEquivalence
            (boundedFlatAffineSupportedSectionForgetPrespectrumMap j)) d ≫
        (stableHomotopyFunctor d).map
          (homotopyFiberLift (boundedFlatAffineSectionOpenPrespectrumMap j)
            (boundedFlatAffineSupportedSectionForgetPrespectrumMap j)
            (boundedFlatAffineSupportedSectionOpenNullHomotopy j)) :=
  mappingConeDesc_connecting _ _ _ _ d

end Quillen.PerfectComplexes
