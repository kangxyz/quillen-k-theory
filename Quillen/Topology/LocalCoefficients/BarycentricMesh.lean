/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.LocalCoefficients.BarycentricGeometry
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Quantitative mesh estimates for actual barycentric simplex maps

The coordinate L1 distance contracts uniformly under every permutation-flag
simplex map. This metric estimate concerns genuine point maps, independently
of any chain-level construction.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open Convexity
open scoped BigOperators Topology

namespace Quillen.BarycentricSubdivision

variable {I J : Type*} [Fintype I] [Fintype J]

/-- The coordinate L1 distance on the standard simplex. -/
def l1Dist (x y : StdSimplex ℝ I) : ℝ := ∑ i, |x.weights i - y.weights i|

theorem l1Dist_nonneg (x y : StdSimplex ℝ I) : 0 ≤ l1Dist x y :=
  Finset.sum_nonneg fun _ _ ↦ abs_nonneg _

/-- Every real standard simplex has coordinate L1 diameter at most two. -/
theorem l1Dist_le_two (x y : StdSimplex ℝ I) : l1Dist x y ≤ 2 := by
  calc
    l1Dist x y ≤ ∑ i, (x.weights i + y.weights i) := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [abs_of_nonneg (x.weights_nonneg i), abs_of_nonneg (y.weights_nonneg i)]
        using abs_sub (x.weights i) (y.weights i)
    _ = 2 := by simp [Finset.sum_add_distrib]; norm_num

/-- Removing the same nonnegative mass at one vertex makes an affine simplex
contract L1 distances by the remaining total mass. -/
theorem l1Dist_affineSimplex_le (v : I → StdSimplex ℝ J) (j₀ : J)
    (c : ℝ) (hc : ∀ i, c ≤ (v i).weights j₀) (x y : StdSimplex ℝ I) :
    l1Dist (affineSimplex v x) (affineSimplex v y) ≤ (1 - c) * l1Dist x y := by
  classical
  let r (i : I) (j : J) := (v i).weights j - if j = j₀ then c else 0
  have hr (i : I) (j : J) : 0 ≤ r i j := by
    dsimp [r]
    split_ifs with h
    · subst j
      exact sub_nonneg.mpr (hc i)
    · simp
  have htotal (i : I) : ∑ j, r i j = 1 - c := by
    simp [r, Finset.sum_sub_distrib]
  have hcoord (j : J) :
      (affineSimplex v x).weights j - (affineSimplex v y).weights j =
        ∑ i, (x.weights i - y.weights i) * r i j := by
    rw [affineSimplex_weights, affineSimplex_weights]
    simp only [r, mul_sub, sub_mul, Finset.sum_sub_distrib, ← Finset.sum_mul]
    simp
  calc
    l1Dist (affineSimplex v x) (affineSimplex v y) =
        ∑ j, |∑ i, (x.weights i - y.weights i) * r i j| := by
      simp only [l1Dist, hcoord]
    _ ≤ ∑ j, ∑ i, |x.weights i - y.weights i| * r i j := by
      apply Finset.sum_le_sum
      intro j _
      simpa only [abs_mul, abs_of_nonneg (hr _ _)] using
        Finset.abs_sum_le_sum_abs (s := Finset.univ)
          (fun i ↦ (x.weights i - y.weights i) * r i j)
    _ = (1 - c) * l1Dist x y := by
      rw [Finset.sum_comm]
      simp only [← Finset.mul_sum, htotal, ← Finset.sum_mul, l1Dist]
      exact mul_comm _ _

/-- The common mass in all vertices of a flag simplex. -/
theorem vertex_first_weight {n : ℕ} (p : Equiv.Perm (Fin (n + 1)))
    (k : Fin (n + 1)) :
    ((n + 1 : ℕ) : ℝ)⁻¹ ≤ (vertex p k).weights (p 0) := by
  classical
  have hmem : p 0 ∈ face p k := by
    exact Finset.mem_image.mpr ⟨0, Finset.mem_Iic.mpr (Fin.zero_le k), rfl⟩
  have hcard : 0 < (face p k).card := (face_nonempty p k).card_pos
  have hle : (face p k).card ≤ n + 1 := by
    simpa using Finset.card_le_univ (face p k)
  have hw : (vertex p k).weights (p 0) = ((face p k).card : ℝ)⁻¹ := by
    simp [vertex, StdSimplex.weights_subBarycenter, Finsupp.single_apply, hmem]
  rw [hw]
  exact inv_anti₀ (by exact_mod_cast hcard) (by exact_mod_cast hle)

/-- The standard barycentric contraction factor, equal to `n / (n + 1)`. -/
def contractionFactor (n : ℕ) : ℝ := 1 - ((n + 1 : ℕ) : ℝ)⁻¹

theorem contractionFactor_nonneg (n : ℕ) : 0 ≤ contractionFactor n := by
  rw [contractionFactor, sub_nonneg]
  exact inv_le_one_of_one_le₀ (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))

theorem contractionFactor_lt_one (n : ℕ) : contractionFactor n < 1 := by
  rw [contractionFactor]
  have h : 0 < ((n + 1 : ℕ) : ℝ)⁻¹ := by positivity
  linarith

/-- Every actual flag simplex uniformly contracts coordinate L1 distance. -/
theorem l1Dist_simplexMap_le {n : ℕ} (p : Equiv.Perm (Fin (n + 1)))
    (x y : StdSimplex ℝ (Fin (n + 1))) :
    l1Dist (simplexMap p x) (simplexMap p y) ≤ contractionFactor n * l1Dist x y :=
  l1Dist_affineSimplex_le (vertex p) (p 0) _ (vertex_first_weight p) x y

/-- An arbitrary sequence of genuine barycentric simplex maps. -/
def iteratedSimplexMap {n : ℕ} : List (Equiv.Perm (Fin (n + 1))) →
    C(StdSimplex ℝ (Fin (n + 1)), StdSimplex ℝ (Fin (n + 1)))
  | [] => ContinuousMap.id _
  | p :: ps => (simplexMap p).comp (iteratedSimplexMap ps)

/-- The contraction multiplies at each stage, uniformly in all flag choices. -/
theorem l1Dist_iteratedSimplexMap_le {n : ℕ}
    (ps : List (Equiv.Perm (Fin (n + 1))))
    (x y : StdSimplex ℝ (Fin (n + 1))) :
    l1Dist (iteratedSimplexMap ps x) (iteratedSimplexMap ps y) ≤
      contractionFactor n ^ ps.length * l1Dist x y := by
  induction ps with
  | nil => simp [iteratedSimplexMap]
  | cons p ps ih =>
    calc
      l1Dist (iteratedSimplexMap (p :: ps) x) (iteratedSimplexMap (p :: ps) y) ≤
          contractionFactor n *
            l1Dist (iteratedSimplexMap ps x) (iteratedSimplexMap ps y) :=
        l1Dist_simplexMap_le p (iteratedSimplexMap ps x) (iteratedSimplexMap ps y)
      _ ≤ contractionFactor n * (contractionFactor n ^ ps.length * l1Dist x y) :=
        mul_le_mul_of_nonneg_left ih (contractionFactor_nonneg n)
      _ = contractionFactor n ^ (p :: ps).length * l1Dist x y := by
        simp [pow_succ, mul_assoc, mul_comm]

/-- Uniform mesh decay, starting from the L1 diameter-two standard simplex. -/
theorem l1Dist_iteratedSimplexMap_le_mesh {n : ℕ}
    (ps : List (Equiv.Perm (Fin (n + 1))))
    (x y : StdSimplex ℝ (Fin (n + 1))) :
    l1Dist (iteratedSimplexMap ps x) (iteratedSimplexMap ps y) ≤
      2 * contractionFactor n ^ ps.length := by
  calc
    _ ≤ contractionFactor n ^ ps.length * l1Dist x y :=
      l1Dist_iteratedSimplexMap_le ps x y
    _ ≤ contractionFactor n ^ ps.length * 2 :=
      mul_le_mul_of_nonneg_left (l1Dist_le_two x y)
        (pow_nonneg (contractionFactor_nonneg n) _)
    _ = _ := mul_comm _ _

/-- The ordinary coordinate sup metric, with the original simplex topology. -/
abbrev coordinateMetric (I : Type*) [Fintype I] : MetricSpace (StdSimplex ℝ I) :=
  (MetricSpace.induced (fun x : StdSimplex ℝ I ↦ (x.weights : I → ℝ))
    (StdSimplex.isEmbedding_toFun_comp_weights ℝ I).injective inferInstance).replaceTopology
      (StdSimplex.isEmbedding_toFun_comp_weights ℝ I).eq_induced

/-- The coordinate metric is bounded above by the coordinate L1 distance. -/
theorem coordinateDist_le_l1Dist (x y : StdSimplex ℝ I) :
    let := coordinateMetric I
    dist x y ≤ l1Dist x y := by
  change dist (x.weights : I → ℝ) y.weights ≤ l1Dist x y
  rw [dist_pi_le_iff (l1Dist_nonneg x y)]
  intro i
  rw [Real.dist_eq]
  exact Finset.single_le_sum (fun j _ ↦ abs_nonneg (x.weights j - y.weights j))
    (Finset.mem_univ i)

/-- Every open cover becomes small after a single uniform finite number of
actual barycentric subdivisions of a continuous singular simplex. The depth
works for every sequence of permutation flags. -/
theorem exists_iteratedSimplexMap_cover_small {X ι : Type*} [TopologicalSpace X]
    {n : ℕ} (σ : C(StdSimplex ℝ (Fin (n + 1)), X)) (U : ι → Set X)
    (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i) :
    ∃ k : ℕ, ∀ ps : List (Equiv.Perm (Fin (n + 1))), ps.length = k →
      ∃ i, Set.range (σ.comp (iteratedSimplexMap ps)) ⊆ U i := by
  let := coordinateMetric (Fin (n + 1))
  have hpre : ∀ i, IsOpen (σ ⁻¹' U i) := fun i ↦ (hU i).preimage σ.continuous
  have hprecover : ⋃ i, σ ⁻¹' U i = Set.univ := by
    ext x
    simpa using hcover (σ x)
  obtain ⟨ε, hε, hLeb⟩ := CompactSpace.lebesgue_number_lemma
    (fun i ↦ σ ⁻¹' U i) hpre hprecover
  have hlim : Filter.Tendsto (fun k : ℕ ↦ 2 * contractionFactor n ^ k)
      Filter.atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (contractionFactor_nonneg n) (contractionFactor_lt_one n)).const_mul 2
  obtain ⟨k, hk⟩ := (hlim.eventually (gt_mem_nhds hε)).exists
  refine ⟨k, fun ps hps ↦ ?_⟩
  have hdiam : Metric.diam (Set.range (iteratedSimplexMap ps)) ≤ ε := by
    apply Metric.diam_le_of_forall_dist_le hε.le
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    exact (coordinateDist_le_l1Dist _ _).trans
      ((l1Dist_iteratedSimplexMap_le_mesh ps x y).trans (by simpa [hps] using hk.le))
  obtain ⟨i, hi⟩ := hLeb (Set.range (iteratedSimplexMap ps))
    (Set.range_nonempty _) hdiam
  exact ⟨i, fun _ ⟨x, hx⟩ ↦ hx ▸ hi (Set.mem_range_self x)⟩

end Quillen.BarycentricSubdivision
