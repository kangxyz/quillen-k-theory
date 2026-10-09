import Quillen.Topology.CubicalSubdivision.Cover
import Quillen.Topology.CubicalSubdivision.Pasting
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let targets := #[`Quillen.Topology.CubicalSubdivision.Grid,
    `Quillen.Topology.CubicalSubdivision.Cover,
    `Quillen.Topology.CubicalSubdivision.Faces,
    `Quillen.Topology.CubicalSubdivision.Pasting]
  let mut count : Nat := 0
  let mut counts : Array Nat := #[0, 0, 0, 0]
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let origin := env.header.moduleNames[index.toNat]!
    let some target := targets.findIdx? (· == origin) | continue
    count := count + 1
    counts := counts.modify target (· + 1)
    let axs ← collectAxioms name
    for ax in axs do
      unless #[`propext,`Classical.choice,`Quot.sound].contains ax do
        throwError "Unsupported axiom {ax} in {name}"
    logInfo m!"ACCEPTED {origin}: {name}: {axs}"
  for i in [:targets.size] do
    unless counts[i]! > 0 do throwError "Missing grid module origin {targets[i]!}"
    logInfo m!"ORIGIN_COUNT {targets[i]!}: {counts[i]!}"
  for forbidden in #[`Quillen.Topology.CubicalSubdivision.Walls,
      `Quillen.Topology.CubicalSubdivision.FaceComplex] do
    if env.header.moduleNames.contains forbidden then throwError "Out-of-scope import {forbidden}"
  unless count == 46 do throwError "Expected 46 grid origins, found {count}"
  logInfo m!"Audited all {count} cubical grid origins."
noncomputable section
open Quillen.CubicalSubdivision
open scoped Topology unitInterval
universe u v
example (n m : ℕ) (k : CellIndex n m) (t : Cube n) (i : Fin n) :
    (cell n m k t i : ℝ) = ((k i : ℝ) + t i) / (m+1) := rfl
example (m : ℕ) (x : unitInterval) : ∃ k t, intervalCell m k t = x := intervalCell_covers m x
example (n m : ℕ) (x : Cube n) : ∃ k t, cell n m k t = x := cell_covers n m x
example (m : ℕ) (x : Cube 0) : ∃ k t, cell 0 m k t = x := cell_covers 0 m x
example (n m : ℕ) : ⋃ k : CellIndex n m, cellSet n m k = Set.univ := cellSet_iUnion n m
example (n m : ℕ) (k : CellIndex n m) : IsClosed (cellSet n m k) := cellSet_isClosed n m k
example (n m : ℕ) (k : CellIndex n m) : Topology.IsClosedEmbedding (cell n m k) :=
  cell_isClosedEmbedding n m k
example (n m : ℕ) (k : CellIndex n m) : Metric.diam (cellSet n m k) ≤ 1/(m+1 : ℝ) :=
  cellSet_diam_le n m k
example (m : ℕ) (k : CellIndex 0 m) : Metric.diam (cellSet 0 m k) ≤ 1/(m+1 : ℝ) :=
  cellSet_diam_le 0 m k
example (n : ℕ) {X : Type u} [TopologicalSpace X] (f : C(Cube n,X)) {J : Type v}
    (U : J → Set X) (hU : ∀ j, IsOpen (U j)) (hc : ∀ x, ∃ j, f x ∈ U j) :
    ∃ m, ∀ k : CellIndex n m, ∃ j, ∀ t, f (cell n m k t) ∈ U j :=
  exists_grid_map_subordinate n f U hU hc
example (n : ℕ) (h : C(Cube n,unitInterval)) :
    ∃ m, ∀ k : CellIndex n m,
      (∀ t, (h (cell n m k t) : ℝ) < 3/4) ∨
      (∀ t, (1/4 : ℝ) < h (cell n m k t)) := exists_grid_height_collars n h
example (n m : ℕ) (k l : CellIndex n m) (i : Fin n)
    (hi : (k i : ℕ)+1 = l i) (hk : ∀ j, j ≠ i → k j = l j) (t : Cube n) :
    cell n m k (Function.update t i 1) = cell n m l (Function.update t i 0) :=
  cell_shared_face n m k l i hi hk t
example (n m : ℕ) (k l : CellIndex n m) (hk : k ≠ l) (s t : Cube n)
    (h : cell n m k s = cell n m l t) :
    s ∈ _root_.Cube.boundary (Fin n) ∧ t ∈ _root_.Cube.boundary (Fin n) :=
  cell_intersection_boundary n m k l hk s t h
example (n m : ℕ) (k : CellIndex n m) (t : Cube n) :
    gridProjection n m ⟨k,t⟩ = cell n m k t := rfl
example (n m : ℕ) : Topology.IsQuotientMap (gridProjection n m) := gridProjection_isQuotientMap n m
example (n m : ℕ) {X : Type u} [TopologicalSpace X]
    (f : ∀ _k : CellIndex n m, C(Cube n,X))
    (hf : ∀ k l s t, cell n m k s = cell n m l t → f k s = f l t) :
    ∃ g : C(Cube n,X), ∀ k t, g (cell n m k t) = f k t := exists_paste n m f hf
example (n m : ℕ) {X : Type u} [TopologicalSpace X] (g h : C(Cube n,X))
    (hh : ∀ k t, g (cell n m k t) = h (cell n m k t)) : g = h := paste_unique n m g h hh
example (n m : ℕ) {X : Type u} [TopologicalSpace X]
    (f : ∀ _k : CellIndex n m, C(Cube n,X)) (g : C(Cube n,X))
    (hg : ∀ k t, g (cell n m k t) = f k t) (S : Set (Cube n)) (a : S → X)
    (ha : ∀ k t (h : cell n m k t ∈ S), f k t = a ⟨cell n m k t,h⟩) :
    ∀ x : S, g x = a x := paste_preserves_subset n m f g hg S a ha

-- Stronger original-endpoint and zero-dimensional tests.
example (m : ℕ) : intervalCell m 0 0 = 0 := by
  apply Subtype.ext
  simp [intervalCell_val]
example (m : ℕ) : intervalCell m ⟨m, Nat.lt_succ_self m⟩ 1 = 1 := by
  apply Subtype.ext
  change ((m : ℝ)+1)/(m+1) = 1
  exact div_self (by positivity)
example (n : ℕ) (k : CellIndex n 0) (t : Cube n) : cell n 0 k t = t := by
  funext i
  apply Subtype.ext
  have hk : k i = 0 := by
    apply Fin.ext
    exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ (k i).isLt)
  simp [cell_apply, hk]
example (n m : ℕ) : Finite (CellIndex n m) := inferInstance
example (n m : ℕ) : CompactSpace (Σ _k : CellIndex n m, Cube n) := inferInstance
example (m : ℕ) (k : CellIndex 0 m) (t : Cube 0) : cell 0 m k t = t := Subsingleton.elim _ _
example (m : ℕ) (k : CellIndex 0 m) : cellSet 0 m k = Set.univ := by
  change Set.range (cell 0 m k) = Set.univ
  exact Set.range_eq_univ.mpr (fun x ↦ ⟨x, Subsingleton.elim _ _⟩)
example (m : ℕ) : Topology.IsQuotientMap (gridProjection 0 m) := gridProjection_isQuotientMap 0 m
example (n m : ℕ) (k : CellIndex n m) (s t : Cube n)
    (h : cell n m k s = cell n m k t) : s = t := cell_injective n m k h
example (n m : ℕ) (k l : CellIndex n m) (s t : Cube n)
    (h : cell n m k s = cell n m l t) :
    (k = l ∧ s = t) ∨ (s ∈ _root_.Cube.boundary (Fin n) ∧ t ∈ _root_.Cube.boundary (Fin n)) := by
  by_cases hkl : k = l
  · subst l
    exact Or.inl ⟨rfl, cell_injective n m k h⟩
  · exact Or.inr (cell_intersection_boundary n m k l hkl s t h)
example (n : ℕ) (h : C(Cube n,unitInterval)) :
    ∃ m, ∀ k : CellIndex n m,
      (∀ x ∈ cellSet n m k, (h x : ℝ) < 3/4) ∨
      (∀ x ∈ cellSet n m k, (1/4 : ℝ) < h x) := by
  obtain ⟨m, hm⟩ := exists_grid_height_collars n h
  refine ⟨m, fun k ↦ ?_⟩
  rcases hm k with hk | hk
  · exact Or.inl (by rintro x ⟨t, rfl⟩; exact hk t)
  · exact Or.inr (by rintro x ⟨t, rfl⟩; exact hk t)
example (m : ℕ) {X : Type u} [TopologicalSpace X]
    (f : ∀ _k : CellIndex 0 m, C(Cube 0,X)) :
    ∃ g : C(Cube 0,X), ∀ k t, g (cell 0 m k t) = f k t := by
  apply exists_paste 0 m f
  intro k l s t _
  have hk : k = l := Subsingleton.elim _ _
  have ht : s = t := Subsingleton.elim _ _
  subst l
  subst t
  rfl
example (n m : ℕ) {X : Type u} [TopologicalSpace X]
    (f : ∀ _k : CellIndex n m, C(Cube n,X))
    (hf : ∀ k l s t, s ∈ _root_.Cube.boundary (Fin n) → t ∈ _root_.Cube.boundary (Fin n) →
      cell n m k s = cell n m l t → f k s = f l t) :
    ∃ g : C(Cube n,X), ∀ k t, g (cell n m k t) = f k t := by
  apply exists_paste n m f
  intro k l s t he
  by_cases hkl : k = l
  · subst l
    have ht : s = t := cell_injective n m k he
    exact congrArg (f k) ht
  · obtain ⟨hs, ht⟩ := cell_intersection_boundary n m k l hkl s t he
    exact hf k l s t hs ht he
