/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRowRefinement
public import Quillen.Waldhausen.SConstruction.Iterated.PushoutConeFiniteStructure

/-!
# Finite range of the original coefficient Bass cone structure

This is the actual raw comparison cone, with the prescribed comparison homotopy.
The four original model corners discharge the complete finite ladder.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open CommRingCat.PolynomialLaurent
universe u
namespace Quillen.PerfectComplexes.CoefficientBassRowRefinement
variable {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R)

/-- The unchanged raw cone structure is bijective on the stated chosen-point groups. -/
theorem source_structure_bijective (n k : ℕ) (hk : k + 2 < 2 * n + 2) :
    Function.Bijective (homotopyGroupMap (N := Fin (k + 2))
      ((source P a).structureMap (n + 3)) ((source P a).map_point (n + 3))) :=
  pushoutCone_structure_bijective
    (prespectrumMap (CoefficientBassRowCone.projection P a))
    (prespectrumMap (CoefficientBassRowCone.projection P a))
    (boundedFlatCoefficientBassSquareComparison P a) n k hk

end Quillen.PerfectComplexes.CoefficientBassRowRefinement
