/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.FullOpenGradedSectionBassSeedNull

/-!
# Independent-coordinate consumers of the original graded Bass seed null

The initial null face is the unchanged forward-T loop with both original cone-null legs.
The final null face and whole basepoint line are fixed. Null time, output-loop time and
prespectrum structure time remain independent, without any localization-null comparison.
-/
@[expose] public section

open Quillen.PerfectComplexes

noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
universe u
namespace QuillenTest.FullOpenGradedSectionBassSeedNull

open Quillen
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R)
  [IsOpenImmersion j] [CompactSpace U]

/-- The initial null face retains the original forward-T loop and its two prescribed null legs. -/
theorem graded_seed_null_original_face (a : Under R) (n : ℕ) (s : unitInterval)
    (x : ((boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j).obj a).space n) :
    Path.toContinuousMap
        ((boundedFlatAffineFullOpenGradedSectionBassSeedNullHomotopy j a).level n (0, x)) s =
      (((boundedFlatAffineFullOpenGradedSectionDiagramLaurentHomotopy j a).postcomp
        (mappingConeInclusion
          (StrictSquare.comparison (boundedFlatAffineFullOpenGradedSectionBassSquare j a))))
        |>.conjugateToZero
          (boundedFlatAffineFullOpenGradedSectionBassNullHomotopy j a)).level n (s, x) :=
  (congrArg (fun γ ↦ Path.toContinuousMap γ s)
    ((boundedFlatAffineFullOpenGradedSectionBassSeedNullHomotopy j a).at_zero n x)).trans
      (boundedFlatAffineFullOpenGradedSectionBassSeedMap_apply j a n x s)

/-- The null ends at the original constant loop and fixes the whole original basepoint line. -/
theorem graded_seed_null_fixed_boundary (a : Under R) (n : ℕ) (r s : unitInterval)
    (x : ((boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j).obj a).space n) :
    Path.toContinuousMap
        ((boundedFlatAffineFullOpenGradedSectionBassSeedNullHomotopy j a).level n (1, x)) s =
        (boundedFlatAffineFullOpenGradedSectionBassCone j a).point n ∧
      Path.toContinuousMap
        ((boundedFlatAffineFullOpenGradedSectionBassSeedNullHomotopy j a).level n
          (r, ((boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j).obj a).point n)) s =
        (boundedFlatAffineFullOpenGradedSectionBassCone j a).point n :=
  ⟨congrArg (fun γ ↦ Path.toContinuousMap γ s)
      ((boundedFlatAffineFullOpenGradedSectionBassSeedNullHomotopy j a).at_one n x),
    congrArg (fun γ ↦ Path.toContinuousMap γ s)
      ((boundedFlatAffineFullOpenGradedSectionBassSeedNullHomotopy j a).at_point n r)⟩

/-- Null, output-loop and structure coordinates remain independent in the actual joint family. -/
theorem graded_seed_null_independent_structure (a : Under R) (n : ℕ) (r s t : unitInterval)
    (x : ((boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j).obj a).space n) :
    Path.toContinuousMap
        ((boundedFlatAffineFullOpenGradedSectionBassSeedNullHomotopy j a).level (n + 1)
          (r, ((boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j).obj a).structureMap
            n x t)) s =
      (boundedFlatAffineFullOpenGradedSectionBassCone j a).structureMap n
        (Path.toContinuousMap
          ((boundedFlatAffineFullOpenGradedSectionBassSeedNullHomotopy j a).level n (r, x)) s) t :=
  (boundedFlatAffineFullOpenGradedSectionBassSeedNullComparison j a).comm n r s x t

end QuillenTest.FullOpenGradedSectionBassSeedNull
