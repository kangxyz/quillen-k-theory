/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.OpenFibration
public import Quillen.Waldhausen.Fibration.ConeComparison

/-!
# The original bounded-flat relative-open cone comparison

The actual acyclic support model, its original inclusion and its entire null track give a
stable equivalence to the original relative-open coarse S-prespectrum. All fibration and
point-set hypotheses are discharged by the existing geometric constructions. This endpoint
is the genuine relative-open model: its comparison with all perfect complexes on the open
still retains the honest K₀-image obstruction. Transport to original supported sections is
separate from this acyclic-model statement.
-/
@[expose] public section

open Quillen.Waldhausen

noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
universe u
namespace Quillen.PerfectComplexes
open Waldhausen Fibration IteratedS
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The original bounded-flat support-acyclic cone descends along its specified null cylinder. -/
def boundedFlatPerfectOpenConeComparison :
    mappingCone (acyclicInclusionPrespectrumMap (boundedFlatPerfectOpenNested j)) ⟶
      originalPrespectrum (boundedFlatPerfectOpenWaldhausen j) :=
  canonicalConePrespectrumMap (boundedFlatPerfectOpenNested j)

/-- Genuine geometric fibration and S-model excision discharge the original stable comparison. -/
theorem boundedFlatPerfectOpenConeComparison_isStableEquivalence :
    IsStableEquivalence (boundedFlatPerfectOpenConeComparison j) :=
  canonicalConePrespectrumMap_isStableEquivalence_of_weak (boundedFlatPerfectOpenNested j)
    (boundedFlatPerfectOpen_canonicalFiberMap_isWeakHomotopyEquivalence j)

/-- The original ambient-to-relative map is the unchanged target face of this cone comparison. -/
theorem boundedFlatPerfectOpenConeComparison_inclusion :
    mappingConeInclusion (acyclicInclusionPrespectrumMap (boundedFlatPerfectOpenNested j)) ≫
        boundedFlatPerfectOpenConeComparison j =
      changeWeakPrespectrumMap (boundedFlatPerfectOpenNested j) :=
  canonicalConePrespectrumMap_inclusion (boundedFlatPerfectOpenNested j)

end Quillen.PerfectComplexes
