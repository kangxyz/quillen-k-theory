/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.UnitInterval
public import Mathlib.Topology.Maps.Proper.Basic

/-! # An actual open cover controlling complete compact boundary tracks

The bad parameters are the image of the closed complement of an open chart
along the entire original boundary track. Compactness of the boundary and
of the time interval makes that image closed in the Hausdorff parameter
space. The complement-fiber property then gives the exact two-chart cover.
Neither endpoint containment nor an arbitrary-closed-set HEP is assumed.
-/
@[expose] public section

noncomputable section
open scoped Topology unitInterval
universe u v w z
namespace Quillen.BoundaryTrackCover
variable {A : Type u} {D : Type v} {F : Type w} {B : Type z}
  [TopologicalSpace A] [TopologicalSpace D] [TopologicalSpace F] [TopologicalSpace B]

/-- Actual parameter values reached by any boundary-track point outside `N`. -/
def bad (i : C(A, D)) (H : C(unitInterval × A, F)) (N : Set F) : Set D :=
  (fun x : unitInterval × A ↦ i x.2) '' (H ⁻¹' Nᶜ)

/-- The chart controlling both the supplied target map and every original
boundary path over the parameter. -/
def U0 (i : C(A, D)) (b : C(D, F)) (H : C(unitInterval × A, F)) (N : Set F) : Set D :=
  b ⁻¹' N \ bad i H N

/-- The chart over the original open base region. -/
def U1 (b : C(D, F)) (q : C(F, B)) (V : Set B) : Set D :=
  (q.comp b) ⁻¹' V

/-- The definition retains every original boundary point and all times. -/
theorem mem_bad_iff (i : C(A, D)) (H : C(unitInterval × A, F)) (N : Set F) (d : D) :
    d ∈ bad i H N ↔ ∃ a : A,i a = d ∧ ∃ t : unitInterval,H (t,a) ∉ N := by
  constructor
  · rintro ⟨⟨t,a⟩,ht,hi⟩
    exact ⟨a,hi,t,ht⟩
  · rintro ⟨a,hi,t,ht⟩
    exact ⟨(t,a),ht,hi⟩

/-- Only the boundary source is compact; the ambient parameter need only be
Hausdorff, and its boundary map need not be injective. -/
theorem isClosed_bad [CompactSpace A] [T2Space D]
    (i : C(A, D)) (H : C(unitInterval × A, F)) {N : Set F} (hN : IsOpen N) :
    IsClosed (bad i H N) := by
  have hK : IsCompact (H ⁻¹' Nᶜ) := (hN.isClosed_compl.preimage H.continuous).isCompact
  exact (hK.image (i.continuous.comp continuous_snd)).isClosed

theorem isOpen_U0 [CompactSpace A] [T2Space D]
    (i : C(A, D)) (b : C(D, F)) (H : C(unitInterval × A, F))
    {N : Set F} (hN : IsOpen N) : IsOpen (U0 i b H N) :=
  (hN.preimage b.continuous).inter (isClosed_bad i H hN).isOpen_compl

theorem isOpen_U1 (b : C(D, F)) (q : C(F, B)) {V : Set B} (hV : IsOpen V) :
    IsOpen (U1 b q V) := hV.preimage (q.comp b).continuous

/-- The original target map lands in the original chart on `U0`. -/
theorem target_mem_of_mem_U0 (i : C(A, D)) (b : C(D, F)) (H : C(unitInterval × A, F))
    (N : Set F) {d : D} (hd : d ∈ U0 i b H N) : b d ∈ N := hd.1

/-- Every point of the entire prescribed boundary track stays in `N` on
`U0`, rather than just its endpoints. -/
theorem track_mem_of_mem_U0 (i : C(A, D)) (b : C(D, F)) (H : C(unitInterval × A, F))
    (N : Set F) {a : A} (ha : i a ∈ U0 i b H N) (t : unitInterval) : H (t,a) ∈ N := by
  by_contra hn
  exact ha.2 ⟨(t,a),hn,rfl⟩

/-- Exact base equality controls the entire original track on `U1`. -/
theorem track_mem_of_mem_U1 (i : C(A, D)) (b : C(D, F)) (H : C(unitInterval × A, F))
    (q : C(F, B)) (V : Set B) (hbase : ∀ t a, q (H (t, a)) = q (b (i a)))
    {a : A} (ha : i a ∈ U1 b q V) (t : unitInterval) : H (t,a) ∈ q ⁻¹' V := by
  change q (H (t,a)) ∈ V
  rw [hbase]
  exact ha

/-- The complement-fiber property rules out every bad track outside `U1`.
No inference from endpoint containment to track containment is used. -/
theorem mem_U0_of_not_mem_U1
    (i : C(A, D)) (b : C(D, F)) (H : C(unitInterval × A, F))
    (q : C(F, B)) (N : Set F) (V : Set B)
    (hbase : ∀ t a, q (H (t, a)) = q (b (i a)))
    (houtside : ∀ y : F,q y ∉ V → y ∈ N)
    {d : D} (hd : d ∉ U1 b q V) : d ∈ U0 i b H N := by
  refine ⟨houtside (b d) hd,?_⟩
  rintro ⟨⟨t,a⟩,hbad,hi⟩
  apply hbad
  apply houtside
  change i a = d at hi
  rw [hbase,hi]
  exact hd

/-- The two literal open-chart candidates cover every original parameter. -/
theorem union_eq_univ
    (i : C(A, D)) (b : C(D, F)) (H : C(unitInterval × A, F))
    (q : C(F, B)) (N : Set F) (V : Set B)
    (hbase : ∀ t a, q (H (t, a)) = q (b (i a)))
    (houtside : ∀ y : F,q y ∉ V → y ∈ N) :
    U0 i b H N ∪ U1 b q V = Set.univ := by
  apply Set.eq_univ_of_forall
  intro d
  by_cases hd : d ∈ U1 b q V
  · exact Or.inr hd
  · exact Or.inl (mem_U0_of_not_mem_U1 i b H q N V hbase houtside hd)

/-- All bad parameters lie over the original open base region. -/
theorem bad_subset_U1
    (i : C(A, D)) (b : C(D, F)) (H : C(unitInterval × A, F))
    (q : C(F, B)) (N : Set F) (V : Set B)
    (hbase : ∀ t a, q (H (t, a)) = q (b (i a)))
    (houtside : ∀ y : F,q y ∉ V → y ∈ N) : bad i H N ⊆ U1 b q V := by
  intro d hd
  by_contra hv
  exact (mem_U0_of_not_mem_U1 i b H q N V hbase houtside hv).2 hd

end Quillen.BoundaryTrackCover
