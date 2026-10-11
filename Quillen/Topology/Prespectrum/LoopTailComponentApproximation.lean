/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Topology.Prespectrum.LoopTailStageStructure
public import Quillen.Topology.Prespectrum.LoopTailBasedApproximation
public import Quillen.Topology.Prespectrum.TelescopeBasedPair

/-!
# The original replacement structure at every positive-stage point

Natural translation of actual loop components, compatible with the original finite transitions
and literal collapse tracks, upgrades the chosen-point comparison to every positive-stage point.
Surjectivity uses a cofinal original-stage representative. Injectivity uses two representatives
with one common basepoint track and the proved finite-stage equality detection. The original T1
hypotheses remain unchanged, and no finite-stage structure is assumed to be an equivalence.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory
open scoped Topology unitInterval

universe u

namespace Quillen.LoopPrespectrum

variable (E : LoopPrespectrum.{u}) [∀ k, T1Space (E.space k)] (i k n : ℕ)

/-- The unchanged structure adjoint is surjective in every finite degree at any displayed
positive-stage loop, using its exact original collapse track. -/
theorem loopTailReplacement_structureMap_surjective_at_stage
    (γ : (loopTailIterate E (i + 1)).space k) :
    Function.Surjective (homotopyGroupMap (N := Fin n)
      ((loopTailReplacement E).structureMap k)
      (x := (Telescope.inclusion (loopTailIterate E) (loopTailTransition E) (i + 1)).map k γ)
      rfl) := by
  let s := (loopTailReplacement E).structureMap k
  let x := (Telescope.inclusion (loopTailIterate E) (loopTailTransition E) (i + 1)).map k γ
  intro b
  let b₀ := (loopComponentHomotopyEquiv (s x) n).symm b
  obtain ⟨a₀, ha₀⟩ := (loopTailReplacement_structureMap_homotopy_bijective E k n).surjective b₀
  obtain ⟨N, hN, aN, hrep⟩ := Telescope.exists_homotopyGroup_representative_ge
    (loopTailIterate E) (loopTailTransition E) k (i + 1) n a₀
  cases N with
  | zero => omega
  | succ j =>
    let γN := (Telescope.transition (loopTailIterate E) (loopTailTransition E)
      (i + 1) (j + 1) hN).map k γ
    let ρ := Telescope.stageTransitionPath (loopTailIterate E) (loopTailTransition E) hN k γ
    let l := (Telescope.inclusion (loopTailIterate E) (loopTailTransition E) (j + 1)).map k
    let c := homotopyGroupMap l rfl (loopComponentHomotopyEquiv γN n aN)
    refine ⟨(pathTransport ρ n).symm c, ?_⟩
    have hbase : homotopyGroupMap s ((loopTailReplacement E).map_point k)
        (homotopyGroupMap l
          ((Telescope.inclusion (loopTailIterate E) (loopTailTransition E) (j + 1)).map_point k)
          aN) = b₀ :=
      (congrArg (homotopyGroupMap s ((loopTailReplacement E).map_point k)) hrep).trans ha₀
    have hc : homotopyGroupMap s rfl c = loopComponentHomotopyEquiv (s (l γN)) n b₀ :=
      (loopTailStructure_inclusion_component E j k n γN aN).trans
        (congrArg (loopComponentHomotopyEquiv (s (l γN)) n) hbase)
    have ht : pathTransport (ρ.map s.continuous) n
        (homotopyGroupMap s rfl ((pathTransport ρ n).symm c)) = homotopyGroupMap s rfl c :=
      (pathTransport_naturality s ρ n ((pathTransport ρ n).symm c)).trans
        (congrArg (homotopyGroupMap s rfl) ((pathTransport ρ n).apply_symm_apply c))
    have hb := loopComponentHomotopyEquiv_pathTransport (ρ.map s.continuous) n b₀
    have hb₀ : loopComponentHomotopyEquiv (s x) n b₀ = b :=
      (loopComponentHomotopyEquiv (s x) n).apply_symm_apply b
    rw [hb₀] at hb
    exact (pathTransport (ρ.map s.continuous) n).injective (ht.trans (hc.trans hb.symm))

/-- Equality after the unchanged structure adjoint reflects original classes at every
positive-stage point, by common-track representability and actual eventual equality. -/
theorem loopTailReplacement_structureMap_injective_at_stage
    (γ : (loopTailIterate E (i + 1)).space k) :
    Function.Injective (homotopyGroupMap (N := Fin n)
      ((loopTailReplacement E).structureMap k)
      (x := (Telescope.inclusion (loopTailIterate E) (loopTailTransition E) (i + 1)).map k γ)
      rfl) := by
  let s := (loopTailReplacement E).structureMap k
  intro a b hab
  obtain ⟨N, hN, aN, bN, ha, hb⟩ := Telescope.exists_homotopyGroup_pair_representative_at
    (loopTailIterate E) (loopTailTransition E) k (i + 1) γ n a b
  cases N with
  | zero => omega
  | succ j =>
    let γN := (Telescope.transition (loopTailIterate E) (loopTailTransition E)
      (i + 1) (j + 1) hN).map k γ
    let ρ := Telescope.stageTransitionPath (loopTailIterate E) (loopTailTransition E) hN k γ
    let l := (Telescope.inclusion (loopTailIterate E) (loopTailTransition E) (j + 1)).map k
    obtain ⟨u, rfl⟩ := (loopComponentHomotopyEquiv γN n).surjective aN
    obtain ⟨v, rfl⟩ := (loopComponentHomotopyEquiv γN n).surjective bN
    have hImage : homotopyGroupMap s rfl
        (homotopyGroupMap l rfl (loopComponentHomotopyEquiv γN n u)) =
        homotopyGroupMap s rfl
          (homotopyGroupMap l rfl (loopComponentHomotopyEquiv γN n v)) := by
      have he := (pathTransport_naturality s ρ n a).symm.trans
        ((congrArg (pathTransport (ρ.map s.continuous) n) hab).trans
          (pathTransport_naturality s ρ n b))
      exact (congrArg (homotopyGroupMap s rfl) ha.symm).trans
        (he.trans (congrArg (homotopyGroupMap s rfl) hb))
    have hChosen := (loopComponentHomotopyEquiv (s (l γN)) n).injective
      ((loopTailStructure_inclusion_component E j k n γN u).symm.trans
        (hImage.trans (loopTailStructure_inclusion_component E j k n γN v)))
    have hStage := (loopTailReplacement_structureMap_homotopy_bijective E k n).injective hChosen
    obtain ⟨M, hM, _hM, heM⟩ := Telescope.exists_eventual_homotopyGroup_eq
      (loopTailIterate E) (loopTailTransition E) k n (i := j + 1) (j := j + 1) u v hStage
    cases M with
    | zero => omega
    | succ m =>
      have hjm : j ≤ m := Nat.le_of_succ_le_succ hM
      let z := (Telescope.transition (loopTailIterate E) (loopTailTransition E)
        (j + 1) (m + 1) hM).map k γN
      have heTrans := (loopTailFiniteTransition_component_naturality E hjm k n γN u).symm.trans
        ((congrArg (loopComponentHomotopyEquiv z n) heM).trans
          (loopTailFiniteTransition_component_naturality E hjm k n γN v))
      have heIncl := congrArg
        (homotopyGroupMap
          ((Telescope.inclusion (loopTailIterate E) (loopTailTransition E) (m + 1)).map k) rfl)
        heTrans
      have ht := (Telescope.stageTransitionPath_homotopyGroupMap
        (loopTailIterate E) (loopTailTransition E) k hM γN n
        (loopComponentHomotopyEquiv γN n u)).trans
          (heIncl.trans (Telescope.stageTransitionPath_homotopyGroupMap
            (loopTailIterate E) (loopTailTransition E) k hM γN n
            (loopComponentHomotopyEquiv γN n v)).symm)
      have heN := (pathTransport
        (Telescope.stageTransitionPath (loopTailIterate E) (loopTailTransition E) hM k γN)
        n).injective ht
      exact (pathTransport ρ n).injective (ha.trans (heN.trans hb.symm))

end Quillen.LoopPrespectrum
