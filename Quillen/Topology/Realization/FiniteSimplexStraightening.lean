/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Realization.SimplexStraighteningStep
public import Quillen.Topology.HomotopyGroups.ZeroDetection
public import Quillen.Topology.Realization.SimplexBoundaryCharts

/-!
# Face-compatible finite relative straightening in every bounded dimension

The dimension induction constructs actual shared homotopies of actual singular
maps. Equal faces use the same index. Boundary overlap is proved from the usual
double-face identity and the previously constructed homotopies. The two base
cases use the empty zero-boundary and the disjoint faces of an interval.
No degeneracy coherence is claimed or needed.
-/

@[expose] public section
noncomputable section

open Convexity
open scoped Topology unitInterval

universe u

namespace Quillen

variable {Z : Type u} [TopologicalSpace Z]

/-- Arbitrary tracks on the two vertices glue on the genuine interval boundary. -/
theorem exists_simplex_boundary_track_one
    (H : Fin 2 → C(StdSimplex ℝ (Fin 1) × I, Z)) :
    ∃ K : C(simplexBoundary 1 × I, Z),
      ∀ (i : Fin 2) (x : StdSimplex ℝ (Fin 1)) (t : I),
        K (simplexBoundaryFace 0 i x, t) = H i (x, t) := by
  apply exists_simplex_boundary_track 0 H
  intro i j x y t h
  by_cases hij : j = i
  · subst j
    have hxy := simplex_map_injective Fin.succAbove_right_injective h
    subst y
    rfl
  · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hij
    have hz := (StdSimplex.mem_range_map_iff (i.succAbove k).succAbove _).mp
      ⟨y, rfl⟩ (i.succAbove k) (by simp [Fin.range_succAbove])
    rw [← h, StdSimplex.weights_map,
      Finsupp.mapDomain_apply_of_injective Fin.succAbove_right_injective] at hz
    have hx := x.total_of_fintype
    have hk : k = 0 := Fin.eq_zero k
    subst k
    rw [Fin.sum_univ_one, hz] at hx
    exact (zero_ne_one hx).elim

/-- The inductive data are actual continuous tracks, not a filler assumption.
Only dimensions strictly below the bound have been straightened. -/
structure PartialSimplexStraightening (n : ℕ) (z : Z)
    (S F : FiniteSimplexFamily Z) (hS : S.FaceClosed) (N : ℕ) where
  /-- The actual shared continuous homotopy track in each degree. -/
  track : ∀ d, {s // s ∈ S d} → C(StdSimplex ℝ (Fin (d + 1)) × I, Z)
  /-- Every track begins at the original singular simplex. -/
  bottom : ∀ d s x, track d s (x, 0) = s.val x
  /-- Selected fixed maps retain every point for every time. -/
  stationary : ∀ d (s : {s // s ∈ S d}), s.val ∈ F d →
    ∀ x t, track d s (x, t) = s.val x
  /-- All already processed face restrictions commute exactly. -/
  face : ∀ d, d + 1 < N → ∀ (s : {s // s ∈ S (d + 1)}) i x t,
    track (d + 1) s (x.map i.succAbove, t) = track d (hS.face s i) (x, t)
  /-- Processed dimensions below the cutoff end at the basepoint. -/
  top : ∀ d, d < N → d < n → ∀ s x, track d s (x, 1) = z

namespace PartialSimplexStraightening

variable {n N : ℕ} {z : Z} {S F : FiniteSimplexFamily Z} {hS : S.FaceClosed}

/-- Stationary maps initialize the induction without any topological hypothesis. -/
def initial (n : ℕ) (z : Z) (S F : FiniteSimplexFamily Z) (hS : S.FaceClosed) :
    PartialSimplexStraightening n z S F hS 0 where
  track d s := ⟨fun x ↦ s.val x.1, by fun_prop⟩
  bottom _ _ _ := rfl
  stationary _ _ _ _ _ := rfl
  face _ h := by omega
  top _ h := by omega

/-- The next boundary is assembled from the previously constructed face tracks.
In positive codimension two, overlap follows from the actual double-face law. -/
theorem exists_boundary (d : ℕ)
    (P : PartialSimplexStraightening n z S F hS (d + 1))
    (s : {s // s ∈ S (d + 1)}) :
    ∃ H : C(simplexBoundary (d + 1) × I, Z),
      ∀ i x t, H (simplexBoundaryFace d i x, t) = P.track d (hS.face s i) (x, t) := by
  cases d with
  | zero => exact exists_simplex_boundary_track_one (fun i ↦ P.track 0 (hS.face s i))
  | succ d =>
    exact exists_simplex_boundary_track_of_family S hS d (P.track d) (P.track (d + 1))
      (P.face d (by omega)) s

/-- Zero-dimensional induction step, using the empty boundary and actual Pi 0. -/
theorem exists_first (n : ℕ) (z : Z) (S F : FiniteSimplexFamily Z)
    (hS : S.FaceClosed)
    (hs : ∀ x : Z, ∀ k : ℕ, k < n → Subsingleton (HomotopyGroup.Pi k Z x))
    (hcollapsed : ∀ d (s : {s // s ∈ S d}), s.val ∈ F d → d < n →
      s.val = ContinuousMap.const _ z) :
    Nonempty (PartialSimplexStraightening n z S F hS 1) := by
  let := isEmpty_simplexBoundary_zero
  let H : {s // s ∈ S 0} → C(simplexBoundary 0 × I, Z) :=
    fun _ ↦ ContinuousMap.const _ z
  obtain ⟨g, K, hK⟩ := exists_finite_simplex_straightening_step n 0 z hs (S 0) (F 0) H
    (fun _ b ↦ isEmptyElim b) (fun _ _ b ↦ isEmptyElim b)
    (fun _ _ b ↦ isEmptyElim b) (hcollapsed 0)
  let P := initial n z S F hS
  let L : {s // s ∈ S 0} → C(StdSimplex ℝ (Fin 1) × I, Z) :=
    fun s ↦ ⟨fun x ↦ K s (x.2, x.1), by fun_prop⟩
  refine ⟨{
    track := Function.update P.track 0 L
    bottom := ?_
    stationary := ?_
    face := by intro d hd; omega
    top := ?_ }⟩
  · intro d s x
    by_cases hd : d = 0
    · subst d
      simp [L]
    · simpa [Function.update_of_ne hd] using P.bottom d s x
  · intro d s hs x t
    by_cases hd : d = 0
    · subst d
      simpa [L] using (hK s).2.2 hs t x
    · simpa [Function.update_of_ne hd] using P.stationary d s hs x t
  · intro d hd hn s x
    have hd0 : d = 0 := by omega
    subst d
    simp [L, (hK s).2.1 hn]

/-- Advance one positive dimension. Above the cutoff only HEP is used. -/
theorem exists_succ (d : ℕ)
    (P : PartialSimplexStraightening n z S F hS (d + 1))
    (hF : F.FaceClosed)
    (hs : ∀ x : Z, ∀ k : ℕ, k < n → Subsingleton (HomotopyGroup.Pi k Z x))
    (hcollapsed : ∀ e (s : {s // s ∈ S e}), s.val ∈ F e → e < n →
      s.val = ContinuousMap.const _ z) :
    Nonempty (PartialSimplexStraightening n z S F hS (d + 2)) := by
  choose H hH using P.exists_boundary d
  have hzero (s : {s // s ∈ S (d + 1)}) (b : simplexBoundary (d + 1)) :
      H s (b, 0) = s.val b.val := by
    obtain ⟨⟨i, x, t⟩, ht⟩ := simplexFaceCylinderCover_surjective d (b, (0 : I))
    have hb : simplexBoundaryFace d i x = b := congrArg Prod.fst ht
    rw [← hb, hH, P.bottom]
    rfl
  have hone (hdn : d + 1 < n) (s : {s // s ∈ S (d + 1)})
      (b : simplexBoundary (d + 1)) : H s (b, 1) = z := by
    obtain ⟨⟨i, x, t⟩, ht⟩ := simplexFaceCylinderCover_surjective d (b, (1 : I))
    have hb : simplexBoundaryFace d i x = b := congrArg Prod.fst ht
    rw [← hb, hH]
    exact P.top d (by omega) (by omega) _ x
  have hfixed (s : {s // s ∈ S (d + 1)}) (hsF : s.val ∈ F (d + 1))
      (b : simplexBoundary (d + 1)) (t : I) : H s (b, t) = s.val b.val := by
    obtain ⟨⟨i, x, u⟩, hu⟩ := simplexFaceCylinderCover_surjective d (b, t)
    have hb : simplexBoundaryFace d i x = b := congrArg Prod.fst hu
    rw [← hb, hH, P.stationary d (hS.face s i) (hF d s.val hsF i)]
    rfl
  obtain ⟨g, K, hK⟩ := exists_finite_simplex_straightening_step n (d + 1) z hs
    (S (d + 1)) (F (d + 1)) H hzero hone hfixed (hcollapsed (d + 1))
  let L : {s // s ∈ S (d + 1)} → C(StdSimplex ℝ (Fin (d + 2)) × I, Z) :=
    fun s ↦ ⟨fun x ↦ K s (x.2, x.1), by fun_prop⟩
  refine ⟨{
    track := Function.update P.track (d + 1) L
    bottom := ?_
    stationary := ?_
    face := ?_
    top := ?_ }⟩
  · intro e s x
    by_cases he : e = d + 1
    · subst e
      simp [L]
    · simpa [Function.update_of_ne he] using P.bottom e s x
  · intro e s hsF x t
    by_cases he : e = d + 1
    · subst e
      simpa [L] using (hK s).2.2 hsF t x
    · simpa [Function.update_of_ne he] using P.stationary e s hsF x t
  · intro e he s i x t
    by_cases hed : e = d
    · subst e
      have hne : d ≠ d + 1 := by omega
      simp only [Function.update_self, Function.update_of_ne hne]
      exact ((hK s).1 (simplexBoundaryFace d i x) t).trans (hH s i x t)
    · have he1 : e + 1 ≠ d + 1 := by omega
      have he0 : e ≠ d + 1 := by omega
      simpa only [Function.update_of_ne he1, Function.update_of_ne he0] using
        P.face e (by omega) s i x t
  · intro e he hn s x
    by_cases hed : e = d + 1
    · subst e
      simp [L, (hK s).2.1 hn]
    · simpa only [Function.update_of_ne hed] using P.top e (by omega) hn s x

end PartialSimplexStraightening

/-- Full relative finite straightening through any chosen dimension bound.
There are no assumed compatibility certificates: all tracks are constructed
from actual low homotopy vanishing and boundary HEP. -/
theorem exists_finite_simplex_straightening (n N : ℕ) (z : Z)
    (S F : FiniteSimplexFamily Z) (hS : S.FaceClosed) (hF : F.FaceClosed)
    (hs : ∀ x : Z, ∀ k : ℕ, k < n → Subsingleton (HomotopyGroup.Pi k Z x))
    (hcollapsed : ∀ d (s : {s // s ∈ S d}), s.val ∈ F d → d < n →
      s.val = ContinuousMap.const _ z) :
    Nonempty (PartialSimplexStraightening n z S F hS N) := by
  induction N with
  | zero => exact ⟨PartialSimplexStraightening.initial n z S F hS⟩
  | succ N ih =>
    cases N with
    | zero => exact PartialSimplexStraightening.exists_first n z S F hS hs hcollapsed
    | succ d =>
      obtain ⟨P⟩ := ih
      exact P.exists_succ d hF hs hcollapsed

/-- Path connectedness supplies degree zero; only positive homotopy groups
strictly below the cutoff are additional assumptions. -/
theorem exists_finite_simplex_straightening_of_pathConnected [PathConnectedSpace Z]
    (n N : ℕ) (z : Z) (S F : FiniteSimplexFamily Z)
    (hS : S.FaceClosed) (hF : F.FaceClosed)
    (hs : ∀ x : Z, ∀ k : ℕ, 0 < k → k < n → Subsingleton (HomotopyGroup.Pi k Z x))
    (hcollapsed : ∀ d (s : {s // s ∈ S d}), s.val ∈ F d → d < n →
      s.val = ContinuousMap.const _ z) :
    Nonempty (PartialSimplexStraightening n z S F hS N) := by
  apply exists_finite_simplex_straightening n N z S F hS hF _ hcollapsed
  intro x k hk
  cases k with
  | zero => exact subsingleton_homotopyGroup_zero x
  | succ k => exact hs x (k + 1) (by omega) hk

namespace PartialSimplexStraightening

variable {n N : ℕ} {z : Z} {S F : FiniteSimplexFamily Z} {hS : S.FaceClosed}

/-- The actual endpoint replacement in each dimension. -/
def endpoint (P : PartialSimplexStraightening n z S F hS N) (d : ℕ)
    (s : {s // s ∈ S d}) : C(StdSimplex ℝ (Fin (d + 1)), Z) :=
  ⟨fun x ↦ P.track d s (x, 1), by fun_prop⟩

/-- Every constructed track is an actual homotopy from the original simplex. -/
def homotopy (P : PartialSimplexStraightening n z S F hS N) (d : ℕ)
    (s : {s // s ∈ S d}) : s.val.Homotopy (P.endpoint d s) where
  toFun x := P.track d s (x.2, x.1)
  continuous_toFun := by fun_prop
  map_zero_left := P.bottom d s
  map_one_left _ := rfl

/-- Endpoint replacements commute literally with every standard face below the bound. -/
theorem endpoint_face (P : PartialSimplexStraightening n z S F hS N)
    (d : ℕ) (hd : d + 1 < N) (s : {s // s ∈ S (d + 1)}) (i : Fin (d + 2)) :
    singularVertexRestriction (P.endpoint (d + 1) s) i.succAbove =
      P.endpoint d (hS.face s i) := by
  ext x
  exact P.face d hd s i x 1

/-- Low-dimensional endpoint maps are exactly the constant singular simplex. -/
theorem endpoint_eq_const (P : PartialSimplexStraightening n z S F hS N)
    (d : ℕ) (hd : d < N) (hn : d < n) (s : {s // s ∈ S d}) :
    P.endpoint d s = ContinuousMap.const _ z := by
  ext x
  exact P.top d hd hn s x

/-- Selected original maps retain every point for the whole homotopy. -/
theorem homotopy_stationary (P : PartialSimplexStraightening n z S F hS N)
    (d : ℕ) (s : {s // s ∈ S d}) (hs : s.val ∈ F d) (t : I)
    (x : StdSimplex ℝ (Fin (d + 1))) : P.homotopy d s (t, x) = s.val x :=
  P.stationary d s hs x t

end PartialSimplexStraightening

end Quillen
