/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassProjectionWholeReference
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassProjectionPathQuarters
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNervePointwiseFamily

/-!
# Pointwise native values of the four original overlap cells

The evaluator is the existing pointwise family. This module asserts its exact values and
retains the original four quarter clocks; joint continuity remains a compact-family statement.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Opposite Convexity
open Quillen.Waldhausen.IteratedS AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.SimplexParameters
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassProjectionPath.WholeReference
open CommonReferenceNerve
variable {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R)
variable {V : Model.{u + 1}}
  (E : V ⟶ modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))

/-- Every whole-nerve point has precisely the old overlap value, in every native degree. -/
theorem pointwise_native (n : ℕ) (y : |nerve (Codiscrete (CommonReferenceNerve.Node E))|)
    (t : unitInterval) (x : (prespectrum V).space n) :
    pointwisePrespectrumFamily (reference P a E) n (family P a E (y, t)) x =
      (boundedFlatCoefficientBassSquareHomotopy P a).level n
        (t, pointwisePrespectrumFamily E n y x) := by
  obtain ⟨k, N, z, hz⟩ := exists_parameter E y
  rw [← hz, family_characteristic, pointwisePrespectrumFamily_parameter,
    pointwisePrespectrumFamily_parameter]
  exact finite_native P a E N n z t x

/-- The positive normalization cell keeps its decreasing first-quarter coordinate. -/
theorem pointwise_edge12 (n : ℕ) (y : |nerve (Codiscrete (CommonReferenceNerve.Node E))|)
    (t : unitInterval) (x : (prespectrum V).space n) :
    pointwisePrespectrumFamily (reference P a E) n
      (FiniteParameter.parameter E (reference P a E) (nodes P a E) (y, edge (k := 4) 1 2 t)) x =
      (boundedFlatCoefficientBassSquareHomotopy P a).level n
        (plusNormalizationTime t, pointwisePrespectrumFamily E n y x) := by
  rw [← parameter_plus_normalization]
  exact pointwise_native P a E n y (plusNormalizationTime t) x

/-- The positive geometric cell keeps its decreasing second-quarter coordinate. -/
theorem pointwise_edge01 (n : ℕ) (y : |nerve (Codiscrete (CommonReferenceNerve.Node E))|)
    (t : unitInterval) (x : (prespectrum V).space n) :
    pointwisePrespectrumFamily (reference P a E) n
      (FiniteParameter.parameter E (reference P a E) (nodes P a E) (y, edge (k := 4) 0 1 t)) x =
      (boundedFlatCoefficientBassSquareHomotopy P a).level n
        (plusGeometricTime t, pointwisePrespectrumFamily E n y x) := by
  rw [← parameter_plus_geometric]
  exact pointwise_native P a E n y (plusGeometricTime t) x

/-- The inverse geometric cell retains its original third-quarter coordinate. -/
theorem pointwise_edge03 (n : ℕ) (y : |nerve (Codiscrete (CommonReferenceNerve.Node E))|)
    (t : unitInterval) (x : (prespectrum V).space n) :
    pointwisePrespectrumFamily (reference P a E) n
      (FiniteParameter.parameter E (reference P a E) (nodes P a E) (y, edge (k := 4) 0 3 t)) x =
      (boundedFlatCoefficientBassSquareHomotopy P a).level n
        (minusGeometricTime t, pointwisePrespectrumFamily E n y x) := by
  rw [← parameter_minus_geometric]
  exact pointwise_native P a E n y (minusGeometricTime t) x

/-- The inverse normalization cell retains its original fourth-quarter coordinate. -/
theorem pointwise_edge34 (n : ℕ) (y : |nerve (Codiscrete (CommonReferenceNerve.Node E))|)
    (t : unitInterval) (x : (prespectrum V).space n) :
    pointwisePrespectrumFamily (reference P a E) n
      (FiniteParameter.parameter E (reference P a E) (nodes P a E) (y, edge (k := 4) 3 4 t)) x =
      (boundedFlatCoefficientBassSquareHomotopy P a).level n
        (minusNormalizationTime t, pointwisePrespectrumFamily E n y x) := by
  rw [← parameter_minus_normalization]
  exact pointwise_native P a E n y (minusNormalizationTime t) x

end Quillen.PerfectComplexes.BassProjectionPath.WholeReference
