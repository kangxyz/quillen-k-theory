/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedSectionOpenLoopCone

/-!
# Original supported loop-cofiber consumers

The original support inclusion, honest coarse relative-open target, full null cylinder and
signed boundary remain visible in these clients. The stable assertion supplies every negative
degree without a topology, excision, or stabilization hypothesis from the caller.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen Quillen.LoopPrespectrum Quillen.PerfectComplexes Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.Tests.SupportedSectionOpenLoopCone
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- Every negative signed group of the actual looped support cone maps bijectively to the endpoint.
-/
theorem original_negative_bijective (r : ℕ) :
    Function.Bijective ((stableHomotopyFunctor (-(r : ℤ) - 1)).map
      (boundedFlatAffineSupportedSectionOpenLoopConeMap j)) := by
  let := boundedFlatAffineSupportedSectionOpenLoopConeMap_isStableEquivalence j (-(r : ℤ) - 1)
  exact ConcreteCategory.bijective_of_isIso _

/-- Original target-loop elements are carried by the unchanged section change of weaknesses. -/
theorem original_target_loop (n : ℕ) (t : unitInterval)
    (γ : Path ((prespectrum (boundedFlatAffineSectionModel R)).point n)
      ((prespectrum (boundedFlatAffineSectionModel R)).point n)) :
    Path.toContinuousMap ((boundedFlatAffineSupportedSectionOpenLoopConeMap j).map n
      ((mappingConeInclusion
        (parameterLoopingMap
          (boundedFlatAffineSupportedSectionForgetPrespectrumMap j))).map n γ)) t =
      (boundedFlatAffineSectionOpenPrespectrumMap j).map n (γ t) := rfl

/-- The original source structure time remains external to the actual null and loop coordinates. -/
theorem original_three_parameters (n : ℕ) (s t r : unitInterval)
    (γ : Path ((prespectrum (boundedFlatAffineSupportedSectionModel j)).point n)
      ((prespectrum (boundedFlatAffineSupportedSectionModel j)).point n)) :
    Path.toContinuousMap
      ((boundedFlatAffineSupportedSectionOpenNullHomotopy j).parameterLoopingNull.level
      (n + 1) (s, (parameterLooping (prespectrum
        (boundedFlatAffineSupportedSectionModel j))).structureMap n γ t)) r =
      (prespectrum (boundedFlatAffineSectionOpenModel j)).structureMap n
        ((boundedFlatAffineSupportedSectionOpenNullHomotopy j).level n (s, γ r)) t :=
  (boundedFlatAffineSupportedSectionOpenNullHomotopy j).comm n s (γ r) t

/-- The actual supported-section inclusion has bijective loop-cofiber maps in negative degree. -/
theorem original_supported_negative_bijective {R : CommRingCat.{u}} {U : Scheme.{u}}
    (j : U ⟶ Spec R) [IsOpenImmersion j] (r : ℕ) :
    Function.Bijective ((stableHomotopyFunctor (-(r : ℤ) - 1)).map
      (mappingConeParameterLoopingComparison
        (boundedFlatAffineSupportedSectionForgetPrespectrumMap j))) := by
  let := Quillen.Waldhausen.IteratedS.mappingConeParameterLoopingComparison_isStableEquivalence
    (boundedFlatAffineSupportedSectionForgetPrespectrumMap j) (-(r : ℤ) - 1)
  exact ConcreteCategory.bijective_of_isIso _

/-- Looping the supported cone descent retains its entire original relative-open null track. -/
theorem original_supported_open_null {R : CommRingCat.{u}} {U : Scheme.{u}}
    (j : U ⟶ Spec R) [IsOpenImmersion j] (n : ℕ) (s t : unitInterval)
    (γ : Path ((prespectrum (boundedFlatAffineSupportedSectionModel j)).point n)
      ((prespectrum (boundedFlatAffineSupportedSectionModel j)).point n)) :
    Path.toContinuousMap
      ((mappingConeParameterLoopingComparison
          (boundedFlatAffineSupportedSectionForgetPrespectrumMap j) ≫
        parameterLoopingMap (boundedFlatAffineSupportedSectionOpenConeMap j)).map n
        (ReducedMappingCone.cylinder
          ((parameterLooping (prespectrum (boundedFlatAffineSupportedSectionModel j))).point n)
          ((parameterLooping (prespectrum (boundedFlatAffineSectionModel R))).point n)
          ((parameterLoopingMap (boundedFlatAffineSupportedSectionForgetPrespectrumMap j)).map n)
          (s, γ))) t =
      (boundedFlatAffineSupportedSectionOpenNullHomotopy j).level n (s, γ t) := rfl

/-- The original supported descent and the literal looped descent are the same whole map. -/
theorem original_supported_open_descent {R : CommRingCat.{u}} {U : Scheme.{u}}
    (j : U ⟶ Spec R) [IsOpenImmersion j] :
    mappingConeParameterLoopingComparison
        (boundedFlatAffineSupportedSectionForgetPrespectrumMap j) ≫
      parameterLoopingMap (boundedFlatAffineSupportedSectionOpenConeMap j) =
    mappingConeDesc (parameterLoopingMap (boundedFlatAffineSupportedSectionForgetPrespectrumMap j))
      (parameterLoopingMap (boundedFlatAffineSectionOpenPrespectrumMap j))
      (boundedFlatAffineSupportedSectionOpenNullHomotopy j).parameterLoopingNull :=
  mappingConeParameterLoopingComparison_desc _ _ _

end Quillen.Tests.SupportedSectionOpenLoopCone
