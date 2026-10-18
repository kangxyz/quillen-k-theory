/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.HomotopyFiber.CappedTriangle
public import Quillen.Topology.HomotopyGroups.SphericalSimplexQuotient
public import Quillen.Topology.HomotopyGroups.CoordinateTransposition

/-!
# The actual radial parameter of the capped spherical triangle

The original source return contracts the three-edge triangle boundary to its
first vertex. On a boundary-constant target simplex, only the middle boundary
edge contributes. The exact formula is the ordered stick-breaking quotient
with one interval reparametrization and a coordinate reversal.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open Convexity
open scoped Topology unitInterval
universe u

namespace Quillen.HomotopyFiber

/-- The actual boundary-return point before composing with the original singular triangle. -/
def triangleRadialPoint (t s : unitInterval) : StdSimplex ℝ (Fin 3) :=
  stdSimplexPathHomotopy standardTriangleBoundary (Path.refl (StdSimplex.single 0)) (t, s)

/-- The middle edge occupies exactly the interval from one quarter to one half. -/
def triangleMiddleParameter (s : unitInterval) : unitInterval :=
  Set.projIcc 0 1 zero_le_one (4 * (s : ℝ) - 1)

/-- The standard edge has precisely its two original barycentric weights. -/
theorem simplexEdgePoint_weights (i j k : Fin 3) (s : unitInterval) :
    (LocalCoefficients.simplexEdgePoint i j s).weights k =
      (if i = k then 1 - (s : ℝ) else 0) + (if j = k then (s : ℝ) else 0) := by
  let a := StdSimplex.homeomorphI.symm s
  have h₁ : a.weights 1 = (s : ℝ) := by
    have he := congrArg Subtype.val (StdSimplex.homeomorphI.apply_symm_apply s)
    exact (StdSimplex.homeomorphI_apply_coe a).symm.trans he
  have h₀ : a.weights 0 = 1 - (s : ℝ) := by
    have ht := a.total_of_fintype
    rw [Fin.sum_univ_two, h₁] at ht
    linarith
  have ha : a = StdSimplex.duple (s := 1 - (s : ℝ)) (t := (s : ℝ)) 0 1
      (sub_nonneg.mpr s.property.2) s.property.1 (by ring) := by
    ext l
    fin_cases l <;> simp [h₀, h₁]
  change (a.map (fun l : Fin 2 ↦ if l = 0 then i else j)).weights k = _
  rw [ha, StdSimplex.map_duple]
  by_cases hik : i = k <;> simp [Finsupp.single_apply, hik]

/-- The first part of the boundary stays on edge 01, including its terminal vertex. -/
theorem standardTriangleBoundary_left_weight (s : unitInterval) (hs : (s : ℝ) ≤ 1 / 4) :
    (standardTriangleBoundary s).weights 2 = 0 := by
  have hhalf : (s : ℝ) ≤ 1 / 2 := by linarith
  have h₄ : 2 * (2 * (s : ℝ)) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> linarith [s.property.1]
  rw [← Path.extend_extends' standardTriangleBoundary s, standardTriangleBoundary,
    Path.extend_trans_of_le_half _ _ hhalf,
    Path.extend_trans_of_le_half _ _ (show (2 : ℝ) * s ≤ 1 / 2 by linarith),
    Path.extend_apply _ h₄]
  change (LocalCoefficients.simplexEdgePoint 0 1 ⟨_, h₄⟩).weights 2 = 0
  simpa using simplexEdgePoint_weights 0 1 2 ⟨_, h₄⟩

/-- The final part of the boundary stays on the reversed edge 02. -/
theorem standardTriangleBoundary_right_weight (s : unitInterval) (hs : 1 / 2 < (s : ℝ)) :
    (standardTriangleBoundary s).weights 1 = 0 := by
  have h₂ : 1 - (2 * (s : ℝ) - 1) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> linarith [s.property.2]
  rw [← Path.extend_extends' standardTriangleBoundary s, standardTriangleBoundary,
    Path.extend_trans_of_half_le _ _ hs.le,
    Path.extend_symm_apply, Path.extend_apply _ h₂]
  change (LocalCoefficients.simplexEdgePoint 0 2 ⟨_, h₂⟩).weights 1 = 0
  simpa using simplexEdgePoint_weights 0 2 1 ⟨_, h₂⟩

/-- The full middle edge has its original increasing orientation and precise affine speed. -/
theorem standardTriangleBoundary_middle (s : unitInterval)
    (hlo : 1 / 4 < (s : ℝ)) (hhi : (s : ℝ) ≤ 1 / 2) :
    standardTriangleBoundary s =
      LocalCoefficients.simplexEdgePoint 1 2 (triangleMiddleParameter s) := by
  have h₄ : 2 * (2 * (s : ℝ)) - 1 ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> linarith
  have hη : 4 * (s : ℝ) - 1 ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> linarith
  rw [← Path.extend_extends' standardTriangleBoundary s, standardTriangleBoundary,
    Path.extend_trans_of_le_half _ _ hhi,
    Path.extend_trans_of_half_le _ _ (show 1 / 2 ≤ (2 : ℝ) * s by linarith),
    Path.extend_apply _ h₄]
  change LocalCoefficients.simplexEdgePoint 1 2 _ = _
  congr 1
  unfold triangleMiddleParameter
  rw [Set.projIcc_of_mem _ hη]
  apply Subtype.ext
  ring

/-- Radial contraction retains the exact original barycentric coefficients. -/
theorem triangleRadialPoint_weights (t s : unitInterval) (i : Fin 3) :
    (triangleRadialPoint t s).weights i =
      (1 - (t : ℝ)) * (standardTriangleBoundary s).weights i +
        (t : ℝ) * (if (0 : Fin 3) = i then 1 else 0) := by
  change (convexCombPair (R := ℝ) (unitInterval.symm t) t
    (unitInterval.nonneg _) (unitInterval.nonneg _) (by simp)
    (standardTriangleBoundary s) (StdSimplex.single 0)).weights i = _
  simp [StdSimplex.weights_convexCombPair, unitInterval.coe_symm_eq, Finsupp.single_apply]

/-- On the contributing middle edge, the source return is exactly the ordered cube quotient. -/
theorem triangleRadialPoint_middle (t s : unitInterval)
    (hlo : 1 / 4 < (s : ℝ)) (hhi : (s : ℝ) ≤ 1 / 2) :
    triangleRadialPoint t s = Cube.stickBreaking 2
      (Fin.cons t (fun _ : Fin 1 ↦ unitInterval.symm (triangleMiddleParameter s))) := by
  ext i
  rw [triangleRadialPoint_weights, standardTriangleBoundary_middle s hlo hhi,
    simplexEdgePoint_weights]
  fin_cases i
  · change (1 - (t : ℝ)) * (0 + 0) + (t : ℝ) * 1 = (t : ℝ)
    ring
  · change (1 - (t : ℝ)) * ((1 - (triangleMiddleParameter s : ℝ)) + 0) +
        (t : ℝ) * 0 = (1 - (t : ℝ)) * (unitInterval.symm (triangleMiddleParameter s) : ℝ)
    rw [unitInterval.coe_symm_eq]
    ring
  · change (1 - (t : ℝ)) * (0 + (triangleMiddleParameter s : ℝ)) + (t : ℝ) * 0 =
        (1 - (t : ℝ)) * ((1 - (unitInterval.symm (triangleMiddleParameter s) : ℝ)) * 1)
    rw [unitInterval.coe_symm_eq]
    ring

end Quillen.HomotopyFiber
