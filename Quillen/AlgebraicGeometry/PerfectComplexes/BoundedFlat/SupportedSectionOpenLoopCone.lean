/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedSectionOpenConeComparison
public import Quillen.Waldhausen.SConstruction.Iterated.ConeParameterLooping

/-!
# The original supported-section cofiber descent after parameter looping

The same complete relative-open nullhomotopy is looped pointwise and descends from the actual
cone of the looped support inclusion. Its factorization is the original loop-cofiber comparison
followed by the loop of the unchanged original cone descent. Genuine model excision proves
stability, retaining the coarse relative-open section endpoint and original signed boundary.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
universe u
namespace Quillen.PerfectComplexes
open Waldhausen.IteratedS
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- The actual looped supported cone descends along the same whole relative-open null track. -/
def boundedFlatAffineSupportedSectionOpenLoopConeMap :
    mappingCone (parameterLoopingMap (boundedFlatAffineSupportedSectionForgetPrespectrumMap j)) ⟶
      parameterLooping (prespectrum (boundedFlatAffineSectionOpenModel j)) :=
  mappingConeDesc (parameterLoopingMap (boundedFlatAffineSupportedSectionForgetPrespectrumMap j))
    (parameterLoopingMap (boundedFlatAffineSectionOpenPrespectrumMap j))
    (boundedFlatAffineSupportedSectionOpenNullHomotopy j).parameterLoopingNull

/-- The factorization retains the unchanged original supported cone descent. -/
theorem boundedFlatAffineSupportedSectionOpenLoopConeMap_factorization :
    mappingConeParameterLoopingComparison
        (boundedFlatAffineSupportedSectionForgetPrespectrumMap j) ≫
        parameterLoopingMap (boundedFlatAffineSupportedSectionOpenConeMap j) =
      boundedFlatAffineSupportedSectionOpenLoopConeMap j :=
  mappingConeParameterLoopingComparison_desc _ _ _

/-- All topology and both excision inputs are discharged for the original supported section models.
-/
theorem boundedFlatAffineSupportedSectionOpenLoopConeMap_isStableEquivalence :
    IsStableEquivalence (boundedFlatAffineSupportedSectionOpenLoopConeMap j) := by
  rw [← boundedFlatAffineSupportedSectionOpenLoopConeMap_factorization]
  exact (Waldhausen.IteratedS.mappingConeParameterLoopingComparison_isStableEquivalence
    (boundedFlatAffineSupportedSectionForgetPrespectrumMap j)).comp
      (parameterLoopingMap_isStableEquivalence _
        (boundedFlatAffineSupportedSectionOpenConeMap_isStableEquivalence j))

/-- The target face remains the original looped change of weak equivalences. -/
theorem boundedFlatAffineSupportedSectionOpenLoopConeMap_inclusion :
    mappingConeInclusion
        (parameterLoopingMap (boundedFlatAffineSupportedSectionForgetPrespectrumMap j)) ≫
        boundedFlatAffineSupportedSectionOpenLoopConeMap j =
      parameterLoopingMap (boundedFlatAffineSectionOpenPrespectrumMap j) :=
  mappingConeInclusion_desc _ _ _

/-- Every cylinder and loop coordinate retains the original relative-open nullhomotopy value. -/
theorem boundedFlatAffineSupportedSectionOpenLoopConeMap_cylinder (n : ℕ) (s t : unitInterval)
    (γ : Path ((prespectrum (boundedFlatAffineSupportedSectionModel j)).point n)
      ((prespectrum (boundedFlatAffineSupportedSectionModel j)).point n)) :
    Path.toContinuousMap ((boundedFlatAffineSupportedSectionOpenLoopConeMap j).map n
      (ReducedMappingCone.cylinder
        ((parameterLooping (prespectrum (boundedFlatAffineSupportedSectionModel j))).point n)
        ((parameterLooping (prespectrum (boundedFlatAffineSectionModel R))).point n)
        ((parameterLoopingMap (boundedFlatAffineSupportedSectionForgetPrespectrumMap j)).map n)
        (s, γ))) t =
      (boundedFlatAffineSupportedSectionOpenNullHomotopy j).level n (s, γ t) := rfl

/-- The original signed cone boundary remains the boundary of the same looped relative-open map. -/
theorem boundedFlatAffineSupportedSectionOpenLoopConeMap_connecting (d : ℤ) :
    (stableHomotopyFunctor (d + 1)).map (boundedFlatAffineSupportedSectionOpenLoopConeMap j) ≫
        stableFiberConnecting
          (parameterLoopingMap (boundedFlatAffineSectionOpenPrespectrumMap j)) d =
      stableMappingConeConnecting
          (parameterLoopingMap (boundedFlatAffineSupportedSectionForgetPrespectrumMap j))
          (Waldhausen.IteratedS.parameterLoopingMap_coneFiber_isStableEquivalence
            (boundedFlatAffineSupportedSectionForgetPrespectrumMap j)) d ≫
        (stableHomotopyFunctor d).map
          (homotopyFiberLift (parameterLoopingMap (boundedFlatAffineSectionOpenPrespectrumMap j))
            (parameterLoopingMap (boundedFlatAffineSupportedSectionForgetPrespectrumMap j))
            (boundedFlatAffineSupportedSectionOpenNullHomotopy j).parameterLoopingNull) :=
  mappingConeDesc_connecting _ _ _ _ d

end Quillen.PerfectComplexes
