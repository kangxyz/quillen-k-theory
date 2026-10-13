/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Prespectrum.LoopTailReplacement
public import Quillen.Topology.HomotopyGroups.Loop.ComponentTranslation

/-!
# Natural component translations in the original loop-tail tower

At every positive stage the unchanged structure and stabilization maps are literal based loop
maps. The same is true for every finite transition in the shifted tower. Consequently the
actual component equivalences form natural squares with the original stage maps in every finite
homotopy degree. No finite-stage structure map is asserted to be invertible; eventual interleaving
and moving-basepoint telescope comparisons remain separate steps.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory
open scoped Topology unitInterval

universe u

namespace Quillen.LoopPrespectrum

variable (E : LoopPrespectrum.{u})

/-- Every positive-stage structure is the unchanged loop map of the previous structure. -/
theorem loopTailIterate_succ_structureMap (i k : ℕ) :
    (loopTailIterate E (i + 1)).structureMap k =
      basedLoopMap ((loopTailIterate E i).structureMap (k + 1))
        ((loopTailIterate E i).map_point (k + 1)) := rfl

/-- The stabilization transition is the same literal loop map, with no coordinate transpose. -/
theorem loopTailTransition_succ_map (i k : ℕ) :
    (loopTailTransition E (i + 1)).map k =
      basedLoopMap ((loopTailTransition E i).map (k + 1))
        ((loopTailTransition E i).map_point (k + 1)) := rfl

/-- Every original finite transition in the positive tail retains the original loop coordinate. -/
theorem loopTailFiniteTransition_apply {i j : ℕ} (h : i ≤ j) (k : ℕ)
    (γ : Path ((loopTailIterate E i).point (k + 1)) ((loopTailIterate E i).point (k + 1)))
    (t : unitInterval) :
    Path.toContinuousMap ((Telescope.transition (loopTailIterate E) (loopTailTransition E)
      (i + 1) (j + 1) (Nat.succ_le_succ h)).map k γ :
        Path ((loopTailIterate E j).point (k + 1)) ((loopTailIterate E j).point (k + 1))) t =
      (Telescope.transition (loopTailIterate E) (loopTailTransition E) i j h).map
        (k + 1) (γ t) := by
  induction j, h using Nat.le_induction with
  | base => rw [Telescope.transition_refl, Telescope.transition_refl]; rfl
  | succ j h ih =>
    rw [Telescope.transition_comp (loopTailIterate E) (loopTailTransition E)
      (i + 1) (j + 1) (j + 2) (Nat.succ_le_succ h) (Nat.le_succ _)]
    rw [Telescope.transition_comp (loopTailIterate E) (loopTailTransition E)
      i j (j + 1) h (Nat.le_succ _)]
    rw [Telescope.transition_succ, Telescope.transition_succ]
    change (loopTailIterate E j).structureMap (k + 1)
      (Path.toContinuousMap ((Telescope.transition (loopTailIterate E) (loopTailTransition E)
        (i + 1) (j + 1) (Nat.succ_le_succ h)).map k γ) t) =
      (loopTailIterate E j).structureMap (k + 1)
        ((Telescope.transition (loopTailIterate E) (loopTailTransition E) i j h).map (k + 1) (γ t))
    exact congrArg ((loopTailIterate E j).structureMap (k + 1)) ih

/-- The actual finite transition is the original based loop map of the preceding transition. -/
theorem loopTailFiniteTransition_map {i j : ℕ} (h : i ≤ j) (k : ℕ) :
    (Telescope.transition (loopTailIterate E) (loopTailTransition E)
      (i + 1) (j + 1) (Nat.succ_le_succ h)).map k =
      basedLoopMap
        ((Telescope.transition (loopTailIterate E) (loopTailTransition E) i j h).map (k + 1))
        ((Telescope.transition (loopTailIterate E) (loopTailTransition E) i j h).map_point
          (k + 1)) := by
  ext γ
  apply Path.ext
  funext t
  exact loopTailFiniteTransition_apply E h k γ t

/-- The original positive-stage stabilization maps preserve natural component translation on
all finite homotopy sets, including degree zero and nonconstant-loop components. -/
theorem loopTailTransition_component_naturality (i k n : ℕ)
    (γ : (loopTailIterate E (i + 1)).space k)
    (a : HomotopyGroup.Pi n ((loopTailIterate E (i + 1)).space k)
      ((loopTailIterate E (i + 1)).point k)) :
    loopComponentHomotopyEquiv ((loopTailTransition E (i + 1)).map k γ) n
      (homotopyGroupMap ((loopTailTransition E (i + 1)).map k)
        ((loopTailTransition E (i + 1)).map_point k) a) =
      homotopyGroupMap ((loopTailTransition E (i + 1)).map k) rfl
        (loopComponentHomotopyEquiv γ n a) :=
  loopComponentHomotopyEquiv_naturality ((loopTailIterate E i).structureMap (k + 1))
    ((loopTailIterate E i).map_point (k + 1)) γ n a

/-- Naturality holds for every original finite transition between positive stages. -/
theorem loopTailFiniteTransition_component_naturality {i j : ℕ} (h : i ≤ j) (k n : ℕ)
    (γ : (loopTailIterate E (i + 1)).space k)
    (a : HomotopyGroup.Pi n ((loopTailIterate E (i + 1)).space k)
      ((loopTailIterate E (i + 1)).point k)) :
    loopComponentHomotopyEquiv
      ((Telescope.transition (loopTailIterate E) (loopTailTransition E)
        (i + 1) (j + 1) (Nat.succ_le_succ h)).map k γ) n
      (homotopyGroupMap ((Telescope.transition (loopTailIterate E) (loopTailTransition E)
        (i + 1) (j + 1) (Nat.succ_le_succ h)).map k)
        ((Telescope.transition (loopTailIterate E) (loopTailTransition E)
          (i + 1) (j + 1) (Nat.succ_le_succ h)).map_point k) a) =
      homotopyGroupMap ((Telescope.transition (loopTailIterate E) (loopTailTransition E)
        (i + 1) (j + 1) (Nat.succ_le_succ h)).map k) rfl
        (loopComponentHomotopyEquiv γ n a) := by
  let f := (Telescope.transition (loopTailIterate E) (loopTailTransition E) i j h).map (k + 1)
  have hf := (Telescope.transition (loopTailIterate E) (loopTailTransition E) i j h).map_point
    (k + 1)
  have H (g : C(Path ((loopTailIterate E i).point (k + 1))
      ((loopTailIterate E i).point (k + 1)), Path ((loopTailIterate E j).point (k + 1))
      ((loopTailIterate E j).point (k + 1))))
      (hg : g (Path.refl ((loopTailIterate E i).point (k + 1))) =
        Path.refl ((loopTailIterate E j).point (k + 1))) (he : g = basedLoopMap f hf) :
      loopComponentHomotopyEquiv (g γ) n (homotopyGroupMap g hg a) =
        homotopyGroupMap g rfl (loopComponentHomotopyEquiv γ n a) := by
    subst g
    exact loopComponentHomotopyEquiv_naturality f hf γ n a
  exact H _ _ (loopTailFiniteTransition_map E h k)

end Quillen.LoopPrespectrum
