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
  let mut seen : NameSet := {}
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let origin := env.header.moduleNames[index.toNat]!
    unless targets.contains origin do continue
    count := count + 1
    seen := seen.insert origin
    let axs ← collectAxioms name
    for ax in axs do
      unless #[`propext,`Classical.choice,`Quot.sound].contains ax do
        throwError "Unsupported axiom {ax} in {name}"
    logInfo m!"ACCEPTED {origin}: {name}: {axs}"
  unless seen.size == 4 do throwError "Missing grid module origin"
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
