/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.Affine.FullOpenGradedSectionBassSeedDiagramNull

/-!
# Coordinate consumers of the original graded seed null naturality

The original coefficient maps preserve the chosen Laurent contraction at its two independent
times. The loop-valued seed null retains a separately evaluated output-loop coordinate. Bundling
with the identity target changes neither the original null time nor its prescribed loop value.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.PolynomialBaseChange Quillen.LoopPrespectrum
open Quillen.PerfectComplexes
universe u
namespace Quillen.Tests.FullOpenGradedSectionBassNullNaturality
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R)
  [IsOpenImmersion j] [CompactSpace U]

/-- Both chosen comparison times survive the original coefficient map without reparametrization. -/
theorem graded_null_original_contraction_times {a b : Under R} (f : a ⟶ b)
    (n : ℕ) (r s : unitInterval)
    (x : ((boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j).obj a).space n) :
    ((boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j).map
        ((laurentUnderFunctor R).map f)).map n
        ((boundedFlatAffineFullOpenGradedSectionDiagramLaurentContraction j a).level n
          (r, (s, x))) =
      (boundedFlatAffineFullOpenGradedSectionDiagramLaurentContraction j b).level n
        (r, (s, ((boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j).map f).map n x)) :=
  boundedFlatAffineFullOpenGradedSectionDiagramLaurentContraction_naturality_apply j f n r s x

/-- Null time and the independent output-loop coordinate survive the original coefficient map. -/
theorem graded_null_original_output_loop {a b : Under R} (f : a ⟶ b)
    (n : ℕ) (r s : unitInterval)
    (x : ((boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j).obj a).space n) :
    (boundedFlatAffineFullOpenGradedSectionBassConeMap j f).map n
        (Path.toContinuousMap
          ((boundedFlatAffineFullOpenGradedSectionBassSeedNullHomotopy j a).level n (r, x)) s) =
      Path.toContinuousMap
        ((boundedFlatAffineFullOpenGradedSectionBassSeedNullHomotopy j b).level n
          (r, ((boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j).map f).map n x)) s :=
  boundedFlatAffineFullOpenGradedSectionBassSeedNullComparison_naturality_apply j f n r s x

/-- The identity-target bundle retains the original K family at every loop coordinate. -/
theorem graded_null_identity_bundle_value (a : Under R) (n : ℕ) (r s : unitInterval)
    (x : ((boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j).obj a).space n) :
    Path.toContinuousMap
        (((boundedFlatAffineFullOpenGradedSectionBassSeedDiagramNull j).homotopy a).level n
          (r, x)) s =
      (boundedFlatAffineFullOpenGradedSectionBassSeedNullComparison j a).level n (r, (s, x)) :=
  boundedFlatAffineFullOpenGradedSectionBassSeedNullHomotopy_apply j a n r s x

end Quillen.Tests.FullOpenGradedSectionBassNullNaturality
