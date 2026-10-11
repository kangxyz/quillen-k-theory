/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.OpenConeComparison

/-!
# Original relative-open cone comparison consumers

The original geometric acyclic inclusion, change of weak equivalences, full null cylinder,
signed fiber boundary and actual negative-degree class lift are retained. The coarse relative
endpoint is kept distinct from the entire perfect K₀ of the open.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
universe u
namespace Quillen.Tests.BoundedFlatOpenConeComparison
open PerfectComplexes Waldhausen Waldhausen.Fibration Waldhausen.IteratedS
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The comparison starts at the original target face and original change-of-weakness map. -/
theorem original_target_face :
    mappingConeInclusion (acyclicInclusionPrespectrumMap (boundedFlatPerfectOpenNested j)) ≫
        boundedFlatPerfectOpenConeComparison j =
      changeWeakPrespectrumMap (boundedFlatPerfectOpenNested j) :=
  boundedFlatPerfectOpenConeComparison_inclusion j

/-- The whole original acyclic nullhomotopy is the actual cone-cylinder value. -/
theorem original_null_cylinder (n : ℕ) (s : unitInterval)
    (x : (originalPrespectrum (acyclicStructure (boundedFlatPerfectOpenNested j))).space n) :
    (boundedFlatPerfectOpenConeComparison j).map n
        (ReducedMappingCone.cylinder
          ((originalPrespectrum (acyclicStructure (boundedFlatPerfectOpenNested j))).point n)
          ((originalPrespectrum (boundedFlatPerfectWaldhausen X)).point n)
          ((acyclicInclusionPrespectrumMap (boundedFlatPerfectOpenNested j)).map n) (s, x)) =
      (acyclicPrespectrumNullhomotopy (boundedFlatPerfectOpenNested j)).level n (s, x) :=
  canonicalConePrespectrumMap_cylinder (boundedFlatPerfectOpenNested j) n s x

/-- Independent cylinder and original structure times survive this same comparison. -/
theorem original_independent_times (n : ℕ) (s t : unitInterval)
    (x : (originalPrespectrum (acyclicStructure (boundedFlatPerfectOpenNested j))).space n) :
    (originalPrespectrum (boundedFlatPerfectOpenWaldhausen j)).structureMap n
        ((boundedFlatPerfectOpenConeComparison j).map n
          (ReducedMappingCone.cylinder
            ((originalPrespectrum (acyclicStructure (boundedFlatPerfectOpenNested j))).point n)
            ((originalPrespectrum (boundedFlatPerfectWaldhausen X)).point n)
            ((acyclicInclusionPrespectrumMap (boundedFlatPerfectOpenNested j)).map n) (s, x))) t =
      (originalPrespectrum (boundedFlatPerfectOpenWaldhausen j)).structureMap n
        ((acyclicPrespectrumNullhomotopy (boundedFlatPerfectOpenNested j)).level n (s, x)) t :=
  congrArg (fun y ↦ (originalPrespectrum (boundedFlatPerfectOpenWaldhausen j)).structureMap n y t)
    (original_null_cylinder j n s x)

/-- Every signed degree uses the same original cone map, with no supplied excision hypothesis. -/
theorem original_signed_stability (d : ℤ) :
    IsIso ((stableHomotopyFunctor d).map (boundedFlatPerfectOpenConeComparison j)) :=
  boundedFlatPerfectOpenConeComparison_isStableEquivalence j d

/-- Negative classes lift through the unchanged map of the actual relative-open cone. -/
theorem original_negative_class_lift (n : ℕ)
    (x : stableHomotopyGroup (originalPrespectrum (boundedFlatPerfectOpenWaldhausen j))
      (-(n : ℤ))) :
    ∃ y, (stableHomotopyFunctor (-(n : ℤ))).map (boundedFlatPerfectOpenConeComparison j) y = x :=
  ((ConcreteCategory.isIso_iff_bijective _).mp (original_signed_stability j (-(n : ℤ)))).2 x

/-- The signed cone boundary lands in the original canonical fiber comparison, with its track. -/
theorem original_signed_boundary (d : ℤ) :
    (stableHomotopyFunctor (d + 1)).map (boundedFlatPerfectOpenConeComparison j) ≫
        stableFiberConnecting (changeWeakPrespectrumMap (boundedFlatPerfectOpenNested j)) d =
      stableMappingConeConnecting (acyclicInclusionPrespectrumMap (boundedFlatPerfectOpenNested j))
          (originalPrespectrum_mappingConeFiberComparison_isStableEquivalence _ _ _) d ≫
        (stableHomotopyFunctor d).map
          (canonicalFiberPrespectrumMap (boundedFlatPerfectOpenNested j)) :=
  canonicalConePrespectrumMap_connecting (boundedFlatPerfectOpenNested j) d

end Quillen.Tests.BoundedFlatOpenConeComparison
