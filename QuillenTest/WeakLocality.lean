/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Topology.HomotopyGroups.WeakLocality

/-!
# Weak locality regression tests

Literal finite cube boundaries, complete stored paths, actual restrictions,
finite chart intersections and empty cases must retain their stated meaning.
-/
@[expose] public section


noncomputable section
open Quillen Quillen.CubicalSubdivision
open scoped Topology unitInterval
universe u v

namespace QuillenTest.WeakLocality
variable {E B : Type u} {J : Type v} [TopologicalSpace E] [TopologicalSpace B]
  (p : C(E, B)) (R : J → Set E) (W : J → Set B)

-- Endpoint membership alone cannot satisfy the definition if an intermediate value escapes.
example (j : J) (z : MappingPath p) (t : unitInterval) (h : z.val.2 t ∉ W j) :
    z ∉ mappingPathChartSet p R W j := fun hz ↦ h (hz.2 t)

-- A full path-chart constraint also forces the original image into that chart at time zero.
example (j : J) (z : MappingPath p) (hz : z ∈ mappingPathChartSet p R W j) :
    p z.val.1 ∈ W j := by
  rw [← z.property]
  exact hz.2 0

-- The displayed restriction is the original forward map, not a replacement equivalence.
example (S : Finset J)
    (x : {x : E // ∀ j ∈ S, x ∈ (Set.univ : Set E) ∧ p x ∈ W j}) :
    (controlledChartMap p (fun _ ↦ Set.univ) W S x).val = p x.val := rfl

abbrev ControlledPaths (S : Finset J) :=
  {z : MappingPath p // ∀ j ∈ S,
    z ∈ mappingPathChartSet p R W j ∧ MappingPath.endpoint p z ∈ W j}

-- Lifted boundary points retain source coordinates and every original path value literally.
example (S : Finset J) (hf : IsWeakHomotopyEquivalence (controlledChartMap p R W S))
    (n : ℕ) (a : C(Boundary n, ControlledPaths p R W S))
    (b : C(Cube n, {y : B // ∀ j ∈ S, y ∈ W j}))
    (hab : ∀ x : Boundary n,
      controlledChartMap (MappingPath.endpoint p) (mappingPathChartSet p R W) W S
        (a x) = b x.val) :
    ∃ c : C(Cube n, ControlledPaths p R W S),
      (∀ x : Boundary n, (c x.val).val.val.1 = (a x).val.val.1) ∧
      (∀ (x : Boundary n) (t : unitInterval),
        (c x.val).val.val.2 t = (a x).val.val.2 t) ∧
      (∀ (x : Cube n) (j : J), j ∈ S → (c x).val.val.1 ∈ R j) ∧
      (∀ (x : Cube n) (j : J), j ∈ S → ∀ t, (c x).val.val.2 t ∈ W j) ∧
      (∀ x : Cube n, MappingPath.endpoint p (c x).val = (b x).val) := by
  obtain ⟨c, hc, hb⟩ := controlled_mappingPath_chart_boundaryLifting p R W S hf n a b hab
  refine ⟨c, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun x ↦ congrArg (fun z : ControlledPaths p R W S ↦ z.val.val.1) (hc x)
  · exact fun x t ↦ congrArg (fun z : ControlledPaths p R W S ↦ z.val.val.2 t) (hc x)
  · exact fun x j hj ↦ ((c x).property j hj).1.1
  · exact fun x j hj t ↦ ((c x).property j hj).1.2 t
  · exact fun x ↦ congrArg Subtype.val (ContinuousMap.congr_fun hb x)

-- No nonempty finite set hypothesis is silently required by the transfer theorem itself.
example (hf : IsWeakHomotopyEquivalence (controlledChartMap p R W ∅)) :
    BoundaryLifting (controlledChartMap (MappingPath.endpoint p)
      (mappingPathChartSet p R W) W ∅) :=
  controlled_mappingPath_chart_boundaryLifting p R W ∅ hf

-- Directly exercise the zero-cube. This does not invoke the weak-equivalence criterion.
example (hf : FiniteCubeStrictHELP p) (y : B) : Nonempty E := by
  let : IsEmpty (CubicalTests.boundary.{u} 0) := ⟨fun z ↦ by
    obtain ⟨i, _⟩ := z.property
    exact Fin.elim0 i⟩
  let a : C(CubicalTests.boundary.{u} 0, E) :=
    ⟨isEmptyElim, continuous_of_discreteTopology⟩
  let b : C(CubicalTests.cube.{u} 0, B) := ContinuousMap.const _ y
  obtain ⟨c, _, _⟩ := hf 0 a b (by ext z; exact isEmptyElim z)
  exact ⟨c (CubicalTests.zero 0)⟩

-- An actually empty overlap has weak empty-to-empty restriction without an extra premise.
theorem emptyRestriction : IsWeakHomotopyEquivalence (restriction p ∅) := by
  exact ⟨fun y ↦ False.elim y.property, fun x ↦ False.elim x.property⟩

example (U V : Set B) (hU : IsOpen U) (hV : IsOpen V) (hc : U ∪ V = Set.univ)
    (hd : U ∩ V = ∅)
    (h0 : IsWeakHomotopyEquivalence (restriction p U))
    (h1 : IsWeakHomotopyEquivalence (restriction p V)) :
    IsWeakHomotopyEquivalence p :=
  isWeakHomotopyEquivalence_of_two_open p U V hU hV hc h0 h1
    (by rw [hd]; exact emptyRestriction p)

-- The theorem has a valid empty-index consumer; coverage forces the target empty.
example [IsEmpty J] (hc : ∀ y : B, ∃ j, y ∈ W j) :
    IsWeakHomotopyEquivalence p := by
  apply isWeakHomotopyEquivalence_of_open_cover p W (fun j ↦ isEmptyElim j) hc
  intro S hS
  obtain ⟨j, _⟩ := hS
  exact isEmptyElim j

variable (hW : ∀ j, IsOpen (W j)) (hc : ∀ y : B, ∃ j, y ∈ W j)
  (hloc : ∀ S : Finset J, S.Nonempty →
    IsWeakHomotopyEquivalence (restriction p {y | ∀ j ∈ S, y ∈ W j}))

-- Global locality yields complete full HELP and the entire prescribed boundary track.
example (n : ℕ) (a : C(CubicalTests.boundary.{u} n, E))
    (b : C(CubicalTests.cube.{u} n, B))
    (H : (p.comp a).Homotopy (b.comp (CubicalTests.boundaryInclusion n).hom)) :
    ∃ c : C(CubicalTests.cube.{u} n, E),
      c.comp (CubicalTests.boundaryInclusion n).hom = a ∧
      ∃ K : (p.comp c).Homotopy b,
        ∀ t z, K (t, z.val) = H (t, z) :=
  (isWeakHomotopyEquivalence_of_open_cover p W hW hc hloc).cube_fullHELP n a b H

example (x : E) :
    Function.Bijective (homotopyGroupMap (N := Fin 0) p (x := x) rfl) :=
  (isWeakHomotopyEquivalence_of_open_cover p W hW hc hloc).homotopy_bijective x 0

example (y : B) : ∃ x : E, Joined (p x) y :=
  (isWeakHomotopyEquivalence_of_open_cover p W hW hc hloc).component_surjective y

example [IsEmpty E] [Nonempty B] : False := by
  obtain ⟨x, _⟩ :=
    (isWeakHomotopyEquivalence_of_open_cover p W hW hc hloc).component_surjective
      (Classical.choice (inferInstance : Nonempty B))
  exact isEmptyElim x

end QuillenTest.WeakLocality
