/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Prespectrum.TelescopeEventualHomotopy
public import Quillen.Topology.Prespectrum.TelescopeStagePaths
public import Quillen.Topology.HomotopyGroups.MovingBasepoint

/-!
# Compact telescope representatives at arbitrary original stage points

A compact relative map based at any displayed original stage point is homotopic into a later
original stage. Its boundary follows the exact finite-prefix contraction track of that point,
and the endpoint basepoint is the unchanged original finite transition. The existing path
transport therefore identifies every original finite-degree class with a later-stage class.
Equality of classes from any fixed original stage point is also detected at a finite stage.

The original stage T1 hypotheses remain explicit. The represented point need not lie in the
chosen component. No Omega-spectrum or complete structure-map weakness is concluded here.
-/

@[expose] public section

open Quillen.Topology


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Set Topology
open scoped unitInterval
open unitInterval

universe u v

namespace Quillen.LoopPrespectrum.Telescope

variable (E : ℕ → LoopPrespectrum.{u}) (f : ∀ i, E i ⟶ E (i + 1)) (k : ℕ)
  [∀ i, T1Space ((E i).space k)]

/-- Compact relative representability retains an arbitrary original stage point and its
actual moving track, without replacing it by the chosen telescope point. -/
theorem exists_stage_representative_at {A : Type v} [TopologicalSpace A] [CompactSpace A]
    (i : ℕ) (x : (E i).space k) (S : Set A) (g : C(A, Space E f k))
    (hg : ∀ a ∈ S, g a = (inclusion E f i).map k x) :
    ∃ N : ℕ, ∃ hi : i ≤ N, ∃ p : C(A, (E N).space k),
      (∀ a ∈ S, p a = (transition E f i N hi).map k x) ∧
      ∃ H : g.Homotopy (((inclusion E f N).map k).comp p),
        ∀ t a, a ∈ S → H (t, a) = stageTransitionPath E f hi k x t := by
  obtain ⟨B, hB⟩ := exists_cylinder_bound E f k g
  let N := max (B + 1) i
  have hBN : B < N := (Nat.lt_succ_self B).trans_le (le_max_left _ _)
  have hi : i ≤ N := le_max_right _ _
  let c := ((collapse E f N).map k).comp g
  have hc (a : A) : c a ∈ range ((inclusion E f N).map k) :=
    collapse_mem_stage E f k g hBN hB a
  let p := liftStage E f k N c hc
  have hp (a : A) : (inclusion E f N).map k (p a) = c a :=
    inclusion_liftStage E f k N c hc a
  refine ⟨N, hi, p, ?_, ?_⟩
  · intro a ha
    apply inclusion_injective E f k N
    rw [hp]
    change (collapse E f N).map k (g a) = _
    rw [hg a ha]
    exact collapse_inclusion E f hi k x
  · refine ⟨{
      toFun := fun z ↦ (collapseHomotopy E f N).level k (z.1, g z.2)
      continuous_toFun := by fun_prop
      map_zero_left := fun a ↦ (collapseHomotopy E f N).at_zero k (g a)
      map_one_left := fun a ↦ ((collapseHomotopy E f N).at_one k (g a)).trans (hp a).symm
      }, ?_⟩
    intro t a ha
    change (collapseHomotopy E f N).level k (t, g a) = _
    rw [hg a ha]
    rfl

/-- Every original finite-degree class at an arbitrary stage point has a genuine later-stage
representative after the exact displayed path transport. This includes degree zero. -/
theorem exists_homotopyGroup_representative_at (i : ℕ) (x : (E i).space k) (n : ℕ)
    (a : HomotopyGroup.Pi n (Space E f k) ((inclusion E f i).map k x)) :
    ∃ N : ℕ, ∃ hi : i ≤ N,
      ∃ b : HomotopyGroup.Pi n ((E N).space k) ((transition E f i N hi).map k x),
        pathTransport (stageTransitionPath E f hi k x) n a =
          homotopyGroupMap ((inclusion E f N).map k) rfl b := by
  induction a using Quotient.inductionOn with
  | h p =>
    obtain ⟨N, hi, q, hq, H, hH⟩ := exists_stage_representative_at E f k i x
      (Cube.boundary (Fin n)) p.val p.property
    let q' : GenLoop (Fin n) ((E N).space k) ((transition E f i N hi).map k x) := ⟨q, hq⟩
    refine ⟨N, hi, Quotient.mk' q', ?_⟩
    exact pathTransport_eq_of_cube_homotopy (stageTransitionPath E f hi k x) n p
      (genLoopPostcomp ((inclusion E f N).map k) rfl q') H hH

/-- Equality at any fixed original stage point is detected after original finite transitions,
without any chosen-component assumption. -/
theorem exists_eventual_homotopyGroup_eq_at (i : ℕ) (x : (E i).space k) (n : ℕ)
    (a b : HomotopyGroup.Pi n ((E i).space k) x)
    (hab : homotopyGroupMap ((inclusion E f i).map k) rfl a =
      homotopyGroupMap ((inclusion E f i).map k) rfl b) :
    ∃ N : ℕ, ∃ hi : i ≤ N,
      homotopyGroupMap ((transition E f i N hi).map k) rfl a =
        homotopyGroupMap ((transition E f i N hi).map k) rfl b := by
  induction a using Quotient.inductionOn with
  | h p =>
    induction b using Quotient.inductionOn with
    | h q =>
      obtain ⟨H⟩ := Quotient.exact hab
      obtain ⟨N, hi, hj, K⟩ := exists_eventual_homotopy E f k
        (Cube.boundary (Fin n)) p.val q.val H
      exact ⟨N, hi, Quotient.sound K⟩

/-- Classes at every actual telescope point are represented at an actual original stage after
the displayed paths. Both the original point and the intermediate stage point are retained. -/
theorem exists_homotopyGroup_representative_from_point (y : Space E f k) (n : ℕ)
    (a : HomotopyGroup.Pi n (Space E f k) y) :
    ∃ i : ℕ, ∃ x : (E i).space k, ∃ γ : Path y ((inclusion E f i).map k x),
      ∃ N : ℕ, ∃ hi : i ≤ N,
        ∃ b : HomotopyGroup.Pi n ((E N).space k) ((transition E f i N hi).map k x),
          pathTransport (stageTransitionPath E f hi k x) n (pathTransport γ n a) =
            homotopyGroupMap ((inclusion E f N).map k) rfl b := by
  obtain ⟨i, x, ⟨γ⟩⟩ := exists_stage_point E f k y
  obtain ⟨N, hi, b, hb⟩ := exists_homotopyGroup_representative_at E f k i x n
    (pathTransport γ n a)
  exact ⟨i, x, γ, N, hi, b, hb⟩

end Quillen.LoopPrespectrum.Telescope
