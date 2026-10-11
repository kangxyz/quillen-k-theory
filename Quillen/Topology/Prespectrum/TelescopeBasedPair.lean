/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Topology.Prespectrum.TelescopeMovingBasepoint
public import Quillen.Topology.Prespectrum.TelescopeHomotopyColimit

/-!
# Simultaneous original-stage representatives with one basepoint track

Two actual classes at an arbitrary displayed original stage point have representatives at one
common later stage, with exactly the same finite-prefix basepoint track. The proof applies
compact relative representability to a disjoint union of the two original cubes. We also retain
the original finite-transition formula for transport of original stage classes and the elementary
cofinal bound on chosen-point representatives.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Set Topology
open scoped unitInterval

universe u

namespace Quillen.LoopPrespectrum.Telescope

variable (E : ℕ → LoopPrespectrum.{u}) (f : ∀ i, E i ⟶ E (i + 1)) (k : ℕ)

/-- The displayed original stage track transports every original class to the actual finite
transition followed by the actual later inclusion. -/
theorem stageTransitionPath_homotopyGroupMap {i N : ℕ} (hi : i ≤ N)
    (x : (E i).space k) (n : ℕ) (a : HomotopyGroup.Pi n ((E i).space k) x) :
    pathTransport (stageTransitionPath E f hi k x) n
      (homotopyGroupMap ((inclusion E f i).map k) rfl a) =
      homotopyGroupMap ((inclusion E f N).map k) rfl
        (homotopyGroupMap ((transition E f i N hi).map k) rfl a) := by
  let H : ((inclusion E f i).map k).Homotopy
      (((inclusion E f N).map k).comp ((transition E f i N hi).map k)) :=
    { toFun z := (collapseHomotopy E f N).level k (z.1, (inclusion E f i).map k z.2)
      continuous_toFun := by fun_prop
      map_zero_left := fun y ↦ (collapseHomotopy E f N).at_zero k ((inclusion E f i).map k y)
      map_one_left := fun y ↦
        ((collapseHomotopy E f N).at_one k ((inclusion E f i).map k y)).trans
          (collapse_inclusion E f hi k y) }
  exact (pathTransport_homotopyGroupMap_homotopy H x n a).trans
    (homotopyGroupMap_comp ((transition E f i N hi).map k) rfl ((inclusion E f N).map k) rfl a)

variable [∀ i, T1Space ((E i).space k)]

/-- A prescribed lower bound can be imposed on a chosen-point original-stage representative. -/
theorem exists_homotopyGroup_representative_ge (m n : ℕ)
    (a : HomotopyGroup.Pi n (Space E f k) (point E f k)) :
    ∃ N : ℕ, ∃ _ : m ≤ N, ∃ b : HomotopyGroup.Pi n ((E N).space k) ((E N).point k),
      homotopyGroupMap ((inclusion E f N).map k) ((inclusion E f N).map_point k) b = a := by
  obtain ⟨i, b, hb⟩ := exists_homotopyGroup_representative E f k n a
  let N := max i m
  have hi : i ≤ N := le_max_left _ _
  refine ⟨N, le_max_right _ _,
    homotopyGroupMap ((transition E f i N hi).map k) ((transition E f i N hi).map_point k) b, ?_⟩
  exact (inclusion_transition_homotopyGroupMap E f hi k n b).symm.trans hb

/-- Two classes at any original stage point use one common later stage and one identical
original moving-basepoint path, in every finite degree. -/
theorem exists_homotopyGroup_pair_representative_at (i : ℕ) (x : (E i).space k) (n : ℕ)
    (a b : HomotopyGroup.Pi n (Space E f k) ((inclusion E f i).map k x)) :
    ∃ N : ℕ, ∃ hi : i ≤ N,
      ∃ a' b' : HomotopyGroup.Pi n ((E N).space k) ((transition E f i N hi).map k x),
        pathTransport (stageTransitionPath E f hi k x) n a =
          homotopyGroupMap ((inclusion E f N).map k) rfl a' ∧
        pathTransport (stageTransitionPath E f hi k x) n b =
          homotopyGroupMap ((inclusion E f N).map k) rfl b' := by
  induction a using Quotient.inductionOn with
  | h p =>
    induction b using Quotient.inductionOn with
    | h q =>
      let S : Set ((Fin n → unitInterval) ⊕ (Fin n → unitInterval)) :=
        {z | Sum.elim (fun t ↦ t ∈ Cube.boundary (Fin n))
          (fun t ↦ t ∈ Cube.boundary (Fin n)) z}
      let g : C((Fin n → unitInterval) ⊕ (Fin n → unitInterval), Space E f k) :=
        ⟨Sum.elim p q, continuous_sum_dom.mpr ⟨p.val.continuous, q.val.continuous⟩⟩
      have hg : ∀ z ∈ S, g z = (inclusion E f i).map k x := by
        intro z hz
        cases z with
        | inl z => exact p.property z hz
        | inr z => exact q.property z hz
      obtain ⟨N, hi, w, hw, H, hH⟩ := exists_stage_representative_at E f k i x S g hg
      let l : C((Fin n → unitInterval), (Fin n → unitInterval) ⊕ (Fin n → unitInterval)) :=
        ⟨Sum.inl, continuous_inl⟩
      let r : C((Fin n → unitInterval), (Fin n → unitInterval) ⊕ (Fin n → unitInterval)) :=
        ⟨Sum.inr, continuous_inr⟩
      let p' : GenLoop (Fin n) ((E N).space k) ((transition E f i N hi).map k x) :=
        ⟨w.comp l, fun z hz ↦ hw (Sum.inl z) hz⟩
      let q' : GenLoop (Fin n) ((E N).space k) ((transition E f i N hi).map k x) :=
        ⟨w.comp r, fun z hz ↦ hw (Sum.inr z) hz⟩
      refine ⟨N, hi, Quotient.mk' p', Quotient.mk' q', ?_, ?_⟩
      · exact pathTransport_eq_of_cube_homotopy (stageTransitionPath E f hi k x) n p
          (genLoopPostcomp ((inclusion E f N).map k) rfl p') (H.compContinuousMap l)
          (fun t z hz ↦ hH t (Sum.inl z) hz)
      · exact pathTransport_eq_of_cube_homotopy (stageTransitionPath E f hi k x) n q
          (genLoopPostcomp ((inclusion E f N).map k) rfl q') (H.compContinuousMap r)
          (fun t z hz ↦ hH t (Sum.inr z) hz)

end Quillen.LoopPrespectrum.Telescope
