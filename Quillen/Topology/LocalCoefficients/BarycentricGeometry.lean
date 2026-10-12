/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Mathlib.Geometry.Convex.ConvexSpace.Barycenter
public import Mathlib.Geometry.Convex.ConvexSpace.AffineMap
public import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Order.Interval.Finset.Fin

/-!
# Genuine affine simplices and barycentric subdivision geometry

Affine combinations of vertices give continuous maps between real standard
simplices. Flags of vertex faces give the actual barycentric subdivision
simplices. These are maps of points, suitable for precomposing singular
simplices, rather than assumed subdivision operators on chains.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open Convexity
open scoped BigOperators Topology

namespace Quillen.BarycentricSubdivision

variable {I J K : Type*}

/-- The affine simplex determined by a tuple of points in a standard simplex. -/
def affineSimplexAffine (v : I → StdSimplex ℝ J) :
    ConvexSpace.AffineMap ℝ (StdSimplex ℝ I) (StdSimplex ℝ J) :=
  StdSimplex.affineMapMk v

/-- Barycentric coordinates of the affine simplex. -/
theorem affineSimplexAffine_weights [Fintype I] (v : I → StdSimplex ℝ J)
    (x : StdSimplex ℝ I) (j : J) :
    (affineSimplexAffine v x).weights j = ∑ i, x.weights i * (v i).weights j := by
  classical
  simp only [affineSimplexAffine, StdSimplex.affineMapMk_apply, iConvexComb,
    StdSimplex.weights_sConvexComb, StdSimplex.weights_map]
  rw [Finsupp.sum_mapDomain_index (by simp) (by simp [add_smul])]
  rw [Finsupp.sum_fintype _ _ (by simp)]
  simp

/-- Affine simplex maps are continuous in the standard simplex topology. -/
theorem continuous_affineSimplexAffine [Finite I] [Finite J] (v : I → StdSimplex ℝ J) :
    Continuous (affineSimplexAffine v) := by
  let := Fintype.ofFinite I
  apply (StdSimplex.isEmbedding_toFun_comp_weights ℝ J).continuous_iff.mpr
  apply continuous_pi
  intro j
  simp only [Function.comp_apply, affineSimplexAffine_weights]
  fun_prop

/-- The continuous affine simplex with the prescribed vertices. -/
def affineSimplex [Finite I] [Finite J] (v : I → StdSimplex ℝ J) :
    C(StdSimplex ℝ I, StdSimplex ℝ J) :=
  ⟨affineSimplexAffine v, continuous_affineSimplexAffine v⟩

theorem affineSimplex_apply [Finite I] [Finite J] (v : I → StdSimplex ℝ J) (x : StdSimplex ℝ I) :
    affineSimplex v x = affineSimplexAffine v x := rfl

@[simp]
theorem affineSimplex_single [Finite I] [Finite J] (v : I → StdSimplex ℝ J) (i : I) :
    affineSimplex v (StdSimplex.single i) = v i :=
  StdSimplex.affineMapMk_single (R := ℝ) v i

theorem affineSimplex_weights [Fintype I] [Finite J] (v : I → StdSimplex ℝ J)
    (x : StdSimplex ℝ I) (j : J) :
    (affineSimplex v x).weights j = ∑ i, x.weights i * (v i).weights j :=
  affineSimplexAffine_weights v x j

/-- Reindexing vertices is exactly precomposition by the standard simplex map.
This includes the deletion of a vertex used in the singular differential. -/
theorem affineSimplex_map [Finite I] [Finite J] [Finite K] (v : I → StdSimplex ℝ J) (f : K → I)
    (x : StdSimplex ℝ K) :
    affineSimplex v (StdSimplex.map f x) = affineSimplex (v ∘ f) x := by
  have h : (affineSimplexAffine v).comp (StdSimplex.affineMap f) =
      affineSimplexAffine (v ∘ f) := by
    apply StdSimplex.affineMap_ext
    intro k
    simp [affineSimplexAffine, Function.comp_def]
  exact congrArg (fun g ↦ g x) h

/-- The affine simplex on the original vertices is the identity. -/
@[simp]
theorem affineSimplex_identity [Finite I] :
    affineSimplex (fun i : I ↦ StdSimplex.single i) = ContinuousMap.id _ := by
  have h : affineSimplexAffine (fun i : I ↦ StdSimplex.single i) =
      ConvexSpace.AffineMap.id (R := ℝ) (StdSimplex ℝ I) := by
    apply StdSimplex.affineMap_ext
    intro i
    simp [affineSimplexAffine]
  exact ContinuousMap.ext (fun x ↦ congrArg (fun f ↦ f x) h)

/-- Affine interpolation commutes with every affine map of standard simplices. -/
theorem affineSimplex_natural [Finite I] [Finite J] [Finite K]
    (v : I → StdSimplex ℝ J)
    (f : ConvexSpace.AffineMap ℝ (StdSimplex ℝ J) (StdSimplex ℝ K))
    (x : StdSimplex ℝ I) : f (affineSimplex v x) = affineSimplex (f ∘ v) x :=
  f.isAffineMap.map_iConvexComb _ _

/-- Composition is obtained by applying the outer affine map to each vertex. -/
theorem affineSimplex_comp [Finite I] [Finite J] [Finite K]
    (v : I → StdSimplex ℝ J) (w : J → StdSimplex ℝ K) :
    (affineSimplex w).comp (affineSimplex v) =
      affineSimplex (affineSimplex w ∘ v) := by
  apply ContinuousMap.ext
  intro x
  exact affineSimplex_natural v (affineSimplexAffine w) x

/-- The barycenter of a nonempty tuple of points. -/
def tupleBarycenter [Fintype I] [Finite J] [Nonempty I] (v : I → StdSimplex ℝ J) : StdSimplex ℝ J :=
  affineSimplex v StdSimplex.barycenter

theorem tupleBarycenter_weights [Fintype I] [Finite J] [Nonempty I]
    (v : I → StdSimplex ℝ J) (j : J) :
    (tupleBarycenter v).weights j =
      (Fintype.card I : ℝ)⁻¹ * ∑ i, (v i).weights j := by
  simp [tupleBarycenter, affineSimplex_weights, StdSimplex.weights_barycenter_apply,
    Finset.mul_sum]


/-- Affine maps commute with the average of a nonempty tuple. -/
theorem tupleBarycenter_natural [Fintype I] [Nonempty I] [Finite J] [Finite K]
    (v : I → StdSimplex ℝ J)
    (f : ConvexSpace.AffineMap ℝ (StdSimplex ℝ J) (StdSimplex ℝ K)) :
    f (tupleBarycenter v) = tupleBarycenter (f ∘ v) := by
  exact f.isAffineMap.map_iConvexComb _ _

/-- A face carrier is the set of points with no coordinates outside that face. -/
def carrier (s : Finset J) : Set (StdSimplex ℝ J) :=
  {x | ∀ j, j ∉ s → x.weights j = 0}

/-- Affine interpolation stays inside every common face carrier. -/
theorem affineSimplex_mem_carrier [Finite I] [Finite J] (v : I → StdSimplex ℝ J) (s : Finset J)
    (hv : ∀ i, v i ∈ carrier s) (x : StdSimplex ℝ I) :
    affineSimplex v x ∈ carrier s := by
  let := Fintype.ofFinite I
  intro j hj
  rw [affineSimplex_weights]
  exact Finset.sum_eq_zero fun i _ ↦ by rw [hv i j hj, mul_zero]

/-- Enlarging a vertex face enlarges its geometric carrier. -/
theorem carrier_mono {s t : Finset J} (hst : s ⊆ t) : carrier s ⊆ carrier t := by
  intro x hx j hj
  exact hx j (fun h ↦ hj (hst h))

/-- Only vertices in the support of the input need lie in the chosen carrier. -/
theorem affineSimplex_mem_carrier_of_support [Finite I] [Finite J]
    (v : I → StdSimplex ℝ J) (s : Finset J) (t : Finset I)
    (hv : ∀ i ∈ t, v i ∈ carrier s) (x : StdSimplex ℝ I) (hx : x ∈ carrier t) :
    affineSimplex v x ∈ carrier s := by
  classical
  let := Fintype.ofFinite I
  intro j hj
  rw [affineSimplex_weights]
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : i ∈ t
  · rw [hv i hi j hj, mul_zero]
  · rw [hx i hi, zero_mul]

/-- The barycenter of a face is supported on that face. -/
theorem subBarycenter_mem_carrier (s : Finset J) (hs : s.Nonempty) :
    StdSimplex.subBarycenter (K := ℝ) s hs ∈ carrier s :=
  StdSimplex.subBarycenter_weights_apply_eq_zero s hs

/-- The initial face of a vertex ordering, including the vertex at `k`. -/
def face {n : ℕ} (p : Equiv.Perm (Fin (n + 1))) (k : Fin (n + 1)) :
    Finset (Fin (n + 1)) := (Finset.Iic k).image p

/-- Every initial face has at least its last vertex. -/
theorem face_nonempty {n : ℕ} (p : Equiv.Perm (Fin (n + 1))) (k : Fin (n + 1)) :
    (face p k).Nonempty := by
  exact ⟨p k, Finset.mem_image.mpr ⟨k, Finset.mem_Iic.mpr le_rfl, rfl⟩⟩

/-- The initial faces form a flag. -/
theorem face_mono {n : ℕ} (p : Equiv.Perm (Fin (n + 1))) : Monotone (face p) := by
  intro i j hij
  exact Finset.image_subset_image (Finset.Iic_subset_Iic.mpr hij)

/-- The vertex of a subdivision simplex associated to an initial face. -/
def vertex {n : ℕ} (p : Equiv.Perm (Fin (n + 1))) (k : Fin (n + 1)) :
    StdSimplex ℝ (Fin (n + 1)) :=
  StdSimplex.subBarycenter (face p k) (face_nonempty p k)

/-- The genuine affine simplex corresponding to a maximal vertex-face flag. -/
def simplexMap {n : ℕ} (p : Equiv.Perm (Fin (n + 1))) :
    C(StdSimplex ℝ (Fin (n + 1)), StdSimplex ℝ (Fin (n + 1))) :=
  affineSimplex (vertex p)

@[simp]
theorem simplexMap_single {n : ℕ} (p : Equiv.Perm (Fin (n + 1)))
    (k : Fin (n + 1)) : simplexMap p (StdSimplex.single k) = vertex p k :=
  affineSimplex_single _ _

/-- The initial face of a subdivision simplex stays in the corresponding
original vertex face. -/
theorem simplexMap_mem_carrier {n : ℕ} (p : Equiv.Perm (Fin (n + 1)))
    (k : Fin (n + 1)) (x : StdSimplex ℝ (Fin (n + 1)))
    (hx : x ∈ carrier (Finset.Iic k)) : simplexMap p x ∈ carrier (face p k) := by
  apply affineSimplex_mem_carrier_of_support (vertex p) (face p k) (Finset.Iic k) _ x hx
  intro i hi
  exact carrier_mono (face_mono p (Finset.mem_Iic.mp hi))
    (subBarycenter_mem_carrier (face p i) (face_nonempty p i))

end Quillen.BarycentricSubdivision
