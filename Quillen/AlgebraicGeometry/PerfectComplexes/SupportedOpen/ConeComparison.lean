/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.SupportedOpen.Fibration
public import Quillen.Waldhausen.Fibration.ConeComparison

/-!
# The original global auxiliary-support coarse cone comparison

For every scheme, open immersion and auxiliary acyclicity open, the original
acyclic-support inclusion and its canonical whole null give a stable cone
comparison with the original supported relative-open coarse S-prespectrum.
The target face and signed connecting formula retain the actual original maps.

The geometric fibration and S-model excision inputs are already proved. No
quasi-compactness or quasi-separatedness is required. The endpoint remains the
coarse relative-open model; no full-open or completed-spectrum comparison is
asserted.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
open Quillen.Waldhausen.Fibration Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens)

/-- The original auxiliary-support cone descends along its specified whole null track. -/
def perfectSupportedOpenConeComparison :
    mappingCone (acyclicInclusionPrespectrumMap (perfectSupportedOpenNested j T)) ⟶
      originalPrespectrum (perfectSupportedOpenWeakWaldhausen j T) :=
  canonicalConePrespectrumMap (perfectSupportedOpenNested j T)

/-- The genuine global supported fibration proves stability of the coarse cone comparison. -/
theorem perfectSupportedOpenConeComparison_isStableEquivalence :
    IsStableEquivalence (perfectSupportedOpenConeComparison j T) :=
  canonicalConePrespectrumMap_isStableEquivalence_of_weak (perfectSupportedOpenNested j T)
    (perfectSupportedOpen_canonicalFiberMap_isWeakHomotopyEquivalence j T)

/-- The cone target face is the unchanged original change-of-weak-equivalences map. -/
theorem perfectSupportedOpenConeComparison_inclusion :
    mappingConeInclusion (acyclicInclusionPrespectrumMap (perfectSupportedOpenNested j T)) ≫
        perfectSupportedOpenConeComparison j T =
      changeWeakPrespectrumMap (perfectSupportedOpenNested j T) :=
  canonicalConePrespectrumMap_inclusion (perfectSupportedOpenNested j T)

/-- Each original cone cylinder retains the specified acyclic nullhomotopy time. -/
theorem perfectSupportedOpenConeComparison_cylinder (n : ℕ) (s : unitInterval)
    (x : (originalPrespectrum (acyclicStructure (perfectSupportedOpenNested j T))).space n) :
    (perfectSupportedOpenConeComparison j T).map n
        (ReducedMappingCone.cylinder
          ((originalPrespectrum (acyclicStructure (perfectSupportedOpenNested j T))).point n)
          ((originalPrespectrum (perfectSupportedWaldhausen T.ι)).point n)
          ((acyclicInclusionPrespectrumMap (perfectSupportedOpenNested j T)).map n) (s, x)) =
      (acyclicPrespectrumNullhomotopy (perfectSupportedOpenNested j T)).level n (s, x) :=
  canonicalConePrespectrumMap_cylinder (perfectSupportedOpenNested j T) n s x

/-- The signed connecting identity keeps the canonical fiber map and the entire original null. -/
theorem perfectSupportedOpenConeComparison_connecting (d : ℤ) :
    (stableHomotopyFunctor (d + 1)).map (perfectSupportedOpenConeComparison j T) ≫
        stableFiberConnecting (changeWeakPrespectrumMap (perfectSupportedOpenNested j T)) d =
      stableMappingConeConnecting
          (acyclicInclusionPrespectrumMap (perfectSupportedOpenNested j T))
          (originalPrespectrum_mappingConeFiberComparison_isStableEquivalence _ _ _) d ≫
        (stableHomotopyFunctor d).map
          (canonicalFiberPrespectrumMap (perfectSupportedOpenNested j T)) :=
  canonicalConePrespectrumMap_connecting (perfectSupportedOpenNested j T) d

end Quillen.PerfectComplexes
