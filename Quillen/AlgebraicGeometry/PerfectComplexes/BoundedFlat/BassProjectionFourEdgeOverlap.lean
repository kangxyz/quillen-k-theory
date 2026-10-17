/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassProjectionFourEdgeRealization
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassProjectionPathQuarters
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveFourEdgeEvaluationCells

/-! The four-edge attachment retains the entire original full-reference overlap family. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open Quillen.NativePathCells
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassProjectionPath.WholeReference.FourEdge
open CommonReferenceNerve
variable {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R)
variable {V : Model.{u + 1}}
  (E : V ⟶ modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))
local notation "J" => BassH0Merge.normalizedMap (polynomialProjection P a)

/-- Equality holds in the full Laurent reference nerve, with all four original quarter clocks. -/
theorem beta_overlap (y : |nerve (Codiscrete (CommonReferenceNerve.Node E))|) (s : I) :
    SSet.toTop.map (beta P a E) (FourEdgeTree.overlap E J (y, s)) =
      family P a E (y, s) := by
  rcases cover s with ⟨u, rfl⟩ | ⟨u, rfl⟩
  · rcases cover (unitInterval.symm u) with ⟨t, ht⟩ | ⟨t, ht⟩
    · have hu : u = unitInterval.symm (lower t) := by
        rw [ht, unitInterval.symm_symm]
      rw [hu, FourEdgeTree.overlap_quarter01,
        ← FourEdgeTree.realizedEdge_comp, beta_edge01]
      change _ = FiniteParameter.parameter E (reference P a E) (nodes P a E)
        (y, BassProjectionPath.parameter (plusGeometricTime t))
      rw [parameter_plus_geometric]
      exact edgeMap_realization P a E 0 1 (by decide) y t
    · have hu : u = unitInterval.symm (upper t) := by
        rw [ht, unitInterval.symm_symm]
      rw [hu, FourEdgeTree.overlap_quarter12,
        ← FourEdgeTree.realizedEdge_comp, beta_edge12]
      change _ = FiniteParameter.parameter E (reference P a E) (nodes P a E)
        (y, BassProjectionPath.parameter (plusNormalizationTime t))
      rw [parameter_plus_normalization]
      exact edgeMap_realization P a E 1 2 (by decide) y t
  · rcases cover u with ⟨t, rfl⟩ | ⟨t, rfl⟩
    · rw [FourEdgeTree.overlap_quarter03,
        ← FourEdgeTree.realizedEdge_comp, beta_edge03]
      change _ = FiniteParameter.parameter E (reference P a E) (nodes P a E)
        (y, BassProjectionPath.parameter (minusGeometricTime t))
      rw [parameter_minus_geometric]
      exact edgeMap_realization P a E 0 3 (by decide) y t
    · rw [FourEdgeTree.overlap_quarter34,
        ← FourEdgeTree.realizedEdge_comp, beta_edge34]
      change _ = FiniteParameter.parameter E (reference P a E) (nodes P a E)
        (y, BassProjectionPath.parameter (minusNormalizationTime t))
      rw [parameter_minus_normalization]
      exact edgeMap_realization P a E 3 4 (by decide) y t

end Quillen.PerfectComplexes.BassProjectionPath.WholeReference.FourEdge
