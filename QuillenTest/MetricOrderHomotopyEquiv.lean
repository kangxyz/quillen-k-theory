/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.MetricOrderComplex.RealizationHomotopyEquiv
public import QuillenTest.MetricOrderReconstruction
import Mathlib.Tactic.NormNum

/-!
# Original representatives throughout the weak/strong homotopy

The weak-target homotopy respects every actual simplex operator at every
interpolation time. In particular, the positive repeated-vertex representative
and its lower-dimensional aggregate give the same full homotopy path. These
checks also retain the exact coordinates and every original vertex.
-/

@[expose] public section
noncomputable section

open CategoryTheory Convexity Opposite Quillen Quillen.MetricOrderComplex
open QuillenTest.MetricOrderRealization QuillenTest.MetricOrderReconstruction
open scoped Simplicial Topology unitInterval

namespace QuillenTest.MetricOrderHomotopyEquiv

/-- All original operators, including faces and degeneracies, commute at every time. -/
theorem blend_operator {P : Type*} [PartialOrder P] {m n : SimplexCategory}
    (a : m ⟶ n) (s : (nerve P).obj (op n))
    (w : StdSimplex ℝ (Fin (m.len + 1))) (t : I) :
    realizationCutoffBlend t (realizationSimplex s (StdSimplex.map a w)) =
      realizationCutoffBlend t (realizationSimplex ((nerve P).map a.op s) w) := by
  rw [realizationSimplex_naturality]

/-- Repeated vertices give the same whole weak-target path as their aggregated edge. -/
theorem repeated_blend (t : I) :
    realizationCutoffBlend t (realizationSimplex repeated sample) =
      realizationCutoffBlend t (realizationSimplex edge collapsed) := by
  rw [repeated_eq_collapsed]

/-- The actual half-maximum formula removes the small endpoint of the repeated-vertex sample. -/
theorem repeated_metric_cutoff :
    (realizationCoordinates (realizationSimplex repeated sample)).cutoff = vertex 0 := by
  classical
  let x := realizationCoordinates (realizationSimplex repeated sample)
  have hx : x.weights = Finsupp.single 0 (5 / 6) + Finsupp.single 1 (1 / 6) :=
    repeated_weights
  have hmax : x.maximum = 5 / 6 := by
    apply le_antisymm
    · apply maximum_le
      intro v
      by_cases h0 : v = 0
      · subst v; norm_num [hx]
      by_cases h1 : v = 1
      · subst v; norm_num [hx]
      norm_num [hx, Finsupp.single_apply, h0, h1, Ne.symm h0, Ne.symm h1]
    · simpa [hx] using weight_le_maximum x 0
  have hw : x.cutoffWeights = Finsupp.single 0 (5 / 12 : ℝ) := by
    ext v
    simp only [cutoffWeights_apply, hx, hmax]
    by_cases h0 : v = 0
    · subst v; norm_num
    by_cases h1 : v = 1
    · subst v; norm_num
    norm_num [Finsupp.single_apply, h0, h1, Ne.symm h0, Ne.symm h1]
  have hm : x.cutoffMass = 5 / 12 := by simp [cutoffMass, hw]
  change x.cutoff = vertex 0
  ext v
  change x.cutoffMass⁻¹ * x.cutoffWeights v = _
  rw [hm, hw]
  by_cases h : v = 0
  · subst v; norm_num
  · simp [h]

/-- The continuous reverse map sends that original sample to the exact original zero vertex. -/
theorem repeated_cutoff_vertex :
    cutoffRealizationMap (realizationCoordinates (realizationSimplex repeated sample)) =
      classifyingSpacePoint (0 : ℕ) := by
  change realizationReconstruction _ = _
  rw [repeated_metric_cutoff, realizationReconstruction_vertex]

/-- The weak interpolation has exactly the already-constructed metric blend coordinates. -/
theorem blend_coordinates {P : Type*} [PartialOrder P] (t : I) (x : |nerve P|) :
    realizationCoordinates (realizationCutoffBlend t x) =
      cutoffBlend t (realizationCoordinates x) :=
  realizationCoordinates_reconstruction _

example : Continuous (fun x : Set.range (simplexCoordinates repeated) ↦
    realizationReconstruction x.1) := continuous_reconstruction_range repeated

example (t : I) : realizationCutoffBlend t (realizationSimplex ascending zeroMiddle) =
    realizationCutoffBlend t (realizationSimplex ((nerve ℕ).δ 1 ascending) edgeWeights) := by
  rw [show realizationSimplex ascending zeroMiddle =
    realizationSimplex ((nerve ℕ).δ 1 ascending) edgeWeights from
      realizationSimplex_naturality _ ascending edgeWeights]

example (t : I) (p : ℕ) :
    (basedRealizationHomotopyEquiv p).leftHomotopy (t, classifyingSpacePoint p) =
      classifyingSpacePoint p := (basedRealizationHomotopyEquiv p).left_fixed t

example (t : I) (p : ℕ) :
    (basedRealizationHomotopyEquiv p).rightHomotopy (t, vertex p) = vertex p :=
  (basedRealizationHomotopyEquiv p).right_fixed t

example (x : |nerve ℕ|) : realizationHomotopyEquiv x = realizationCoordinates x := rfl

example (x : MetricOrderComplex ℕ) :
    realizationCoordinates (realizationHomotopyEquiv.invFun x) = x.cutoff :=
  realizationCoordinates_cutoffRealization x

end QuillenTest.MetricOrderHomotopyEquiv
