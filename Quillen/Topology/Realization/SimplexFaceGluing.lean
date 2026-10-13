/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Realization.SimplexBoundary
public import Quillen.Topology.Realization.Prism
public import Mathlib.Topology.ContinuousMap.Basic

/-!
# Genuine gluing of face homotopies on a simplex boundary

The standard faces, including their full time coordinate, give a compact
Hausdorff quotient cover of the actual geometric boundary cylinder. Face
tracks which agree at each common geometric point therefore descend to one
continuous boundary track, with exact restriction equations. No choice of
independent boundary occurrences is made.
-/

@[expose] public section
noncomputable section

open Convexity Topology
open scoped unitInterval

universe u

namespace Quillen

/-- The standard increasing face map with its actual boundary membership. -/
def simplexBoundaryFace (d : ℕ) (i : Fin (d + 2)) :
    C(StdSimplex ℝ (Fin (d + 1)), simplexBoundary (d + 1)) where
  toFun x := ⟨x.map i.succAbove, i,
    (StdSimplex.mem_range_map_iff i.succAbove _).mp ⟨x, rfl⟩ i
      (by simp [Fin.range_succAbove])⟩
  continuous_toFun := (StdSimplex.continuous_map ℝ i.succAbove).subtype_mk _

/-- All standard faces cover the whole boundary, retaining the time coordinate. -/
def simplexFaceCylinderCover (d : ℕ) :
    C(Fin (d + 2) × (StdSimplex ℝ (Fin (d + 1)) × I), simplexBoundary (d + 1) × I) where
  toFun x := (simplexBoundaryFace d x.1 x.2.1, x.2.2)
  continuous_toFun := by
    rw [continuous_prod_of_discrete_left]
    intro i
    exact ((simplexBoundaryFace d i).continuous.comp continuous_fst).prodMk continuous_snd

/-- Every boundary point is represented by a literal standard face. -/
theorem simplexFaceCylinderCover_surjective (d : ℕ) :
    Function.Surjective (simplexFaceCylinderCover d) := by
  rintro ⟨b, t⟩
  obtain ⟨i, hi⟩ := b.property
  have hb : b.val ∈ Set.range (StdSimplex.map i.succAbove) := by
    rw [StdSimplex.mem_range_map_iff]
    intro j hj
    have hji : j = i := by simpa [Fin.range_succAbove] using hj
    simpa only [hji] using hi
  obtain ⟨x, hx⟩ := hb
  exact ⟨(i, x, t), Prod.ext (Subtype.ext hx) rfl⟩

/-- The finite compact face-cylinder cover is an actual quotient map. -/
theorem simplexFaceCylinderCover_isQuotientMap (d : ℕ) :
    IsQuotientMap (simplexFaceCylinderCover d) :=
  IsQuotientMap.of_surjective_continuous (simplexFaceCylinderCover_surjective d)
    (simplexFaceCylinderCover d).continuous

variable {Z : Type u} [TopologicalSpace Z]

/-- Compatible face tracks descend to a genuine continuous boundary homotopy.
Compatibility concerns actual points in intersecting faces, not face labels. -/
theorem exists_simplex_boundary_track (d : ℕ)
    (H : Fin (d + 2) → C(StdSimplex ℝ (Fin (d + 1)) × I, Z))
    (hcompat : ∀ (i j : Fin (d + 2)) (x y : StdSimplex ℝ (Fin (d + 1))) (t : I),
      x.map i.succAbove = y.map j.succAbove → H i (x, t) = H j (y, t)) :
    ∃ K : C(simplexBoundary (d + 1) × I, Z),
      ∀ (i : Fin (d + 2)) (x : StdSimplex ℝ (Fin (d + 1))) (t : I),
        K (simplexBoundaryFace d i x, t) = H i (x, t) := by
  let G : C(Fin (d + 2) × (StdSimplex ℝ (Fin (d + 1)) × I), Z) := {
    toFun x := H x.1 x.2
    continuous_toFun := continuous_prod_of_discrete_left.mpr fun i ↦ (H i).continuous }
  have hG : Function.FactorsThrough G (simplexFaceCylinderCover d) := by
    rintro ⟨i, x, t⟩ ⟨j, y, s⟩ h
    have ht : t = s := congrArg Prod.snd h
    subst s
    exact hcompat i j x y t (congrArg (fun z ↦ z.1.val) h)
  let K := (simplexFaceCylinderCover_isQuotientMap d).lift G hG
  refine ⟨K, fun i x t ↦ ?_⟩
  exact ContinuousMap.congr_fun
    ((simplexFaceCylinderCover_isQuotientMap d).lift_comp G hG) (i, x, t)

end Quillen

namespace Quillen

/-- An injective vertex map is injective on actual geometric simplices. -/
theorem simplex_map_injective {A B : Type*} {f : A → B} (hf : Function.Injective f) :
    Function.Injective (StdSimplex.map (R := ℝ) f) := by
  intro x y h
  apply StdSimplex.ext
  ext a
  have ha := congrArg (fun z : StdSimplex ℝ B ↦ z.weights (f a)) h
  simpa only [StdSimplex.weights_map, Finsupp.mapDomain_apply_of_injective hf] using ha

/-- Two distinct intersecting faces come from the same actual codimension-two
simplex, with the standard increasing vertex order on both restrictions. -/
theorem simplex_faces_common_source (d : ℕ) (i : Fin (d + 3)) (k : Fin (d + 2))
    (x y : StdSimplex ℝ (Fin (d + 2)))
    (h : x.map i.succAbove = y.map (i.succAbove k).succAbove) :
    ∃ q : StdSimplex ℝ (Fin (d + 1)),
      q.map k.succAbove = x ∧ q.map (k.predAbove i).succAbove = y := by
  have hx : x.weights k = 0 := by
    have hz := (StdSimplex.mem_range_map_iff (i.succAbove k).succAbove _).mp
      ⟨y, rfl⟩ (i.succAbove k) (by simp [Fin.range_succAbove])
    rw [← h, StdSimplex.weights_map,
      Finsupp.mapDomain_apply_of_injective Fin.succAbove_right_injective] at hz
    exact hz
  have hxrange : x ∈ Set.range (StdSimplex.map k.succAbove) := by
    rw [StdSimplex.mem_range_map_iff]
    intro a ha
    have hak : a = k := by simpa [Fin.range_succAbove] using ha
    simpa only [hak] using hx
  obtain ⟨q, hq⟩ := hxrange
  refine ⟨q, hq, simplex_map_injective (f := (i.succAbove k).succAbove)
    Fin.succAbove_right_injective ?_⟩
  rw [← h, ← hq, ← StdSimplex.map_comp, ← StdSimplex.map_comp]
  congr 1
  funext a
  exact Fin.succAbove_succAbove_succAbove_predAbove i k a

variable {Z : Type u} [TopologicalSpace Z]

/-- Ordinary double-face compatibility implies pointwise overlap agreement;
there is no additional matching condition on geometric intersections. -/
theorem simplex_face_tracks_compatible (d : ℕ)
    (H : Fin (d + 3) → C(StdSimplex ℝ (Fin (d + 2)) × I, Z))
    (hfaces : ∀ (i : Fin (d + 3)) (k : Fin (d + 2))
      (q : StdSimplex ℝ (Fin (d + 1))) (t : I),
      H i (q.map k.succAbove, t) =
        H (i.succAbove k) (q.map (k.predAbove i).succAbove, t))
    (i j : Fin (d + 3)) (x y : StdSimplex ℝ (Fin (d + 2))) (t : I)
    (h : x.map i.succAbove = y.map j.succAbove) : H i (x, t) = H j (y, t) := by
  by_cases hij : j = i
  · subst j
    have hxy := simplex_map_injective Fin.succAbove_right_injective h
    subst y
    rfl
  · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hij
    obtain ⟨q, rfl, rfl⟩ := simplex_faces_common_source d i k x y h
    exact hfaces i k q t

/-- The usual simplicial double-face equations already suffice for continuous
boundary descent, with the complete time coordinate unchanged. -/
theorem exists_simplex_boundary_track_of_faces (d : ℕ)
    (H : Fin (d + 3) → C(StdSimplex ℝ (Fin (d + 2)) × I, Z))
    (hfaces : ∀ (i : Fin (d + 3)) (k : Fin (d + 2))
      (q : StdSimplex ℝ (Fin (d + 1))) (t : I),
      H i (q.map k.succAbove, t) =
        H (i.succAbove k) (q.map (k.predAbove i).succAbove, t)) :
    ∃ K : C(simplexBoundary (d + 2) × I, Z),
      ∀ (i : Fin (d + 3)) (x : StdSimplex ℝ (Fin (d + 2))) (t : I),
        K (simplexBoundaryFace (d + 1) i x, t) = H i (x, t) :=
  exists_simplex_boundary_track (d + 1) H (simplex_face_tracks_compatible d H hfaces)

end Quillen
