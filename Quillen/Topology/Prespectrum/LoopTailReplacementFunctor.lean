/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Prespectrum.LoopTailFunctor
public import Quillen.Topology.Prespectrum.LoopTailReplacement

/-!
# The original loop-tail replacement as a strict functor

Strict original maps act on every literal loop-tail iterate and commute with its original
stabilization transition. The existing strict telescope map therefore acts on each whole original
cylinder without changing its height. Its genuine identity and composition laws give an actual
endofunctor, and the unchanged initial inclusions give a strict natural transformation.
These constructions need no T1 assumption; stable and Omega comparisons are separate results.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory
open scoped Topology unitInterval

universe u

namespace Quillen.LoopPrespectrum

/-- Iterate the actual untransposed loop-tail functor on an original strict map. -/
def loopTailIterateMap {E F : LoopPrespectrum.{u}} (f : E ⟶ F) :
    (i : ℕ) → loopTailIterate E i ⟶ loopTailIterate F i
  | 0 => f
  | i + 1 => loopTailFunctor.map (loopTailIterateMap f i)

/-- The whole new loop coordinate is evaluated before the previous original stage map. -/
@[simp] theorem loopTailIterateMap_succ_apply {E F : LoopPrespectrum.{u}} (f : E ⟶ F)
    (i k : ℕ) (γ : Path ((loopTailIterate E i).point (k + 1))
      ((loopTailIterate E i).point (k + 1))) (t : unitInterval) :
    Path.toContinuousMap ((loopTailIterateMap f (i + 1)).map k γ) t =
      (loopTailIterateMap f i).map (k + 1) (γ t) := rfl

/-- Iteration preserves the literal identity maps, not merely their homotopy classes. -/
@[simp] theorem loopTailIterateMap_id (E : LoopPrespectrum.{u}) (i : ℕ) :
    loopTailIterateMap (𝟙 E) i = 𝟙 (loopTailIterate E i) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    change loopTailFunctor.map (loopTailIterateMap (𝟙 E) i) = _
    rw [ih]
    exact loopTailFunctor.map_id _

/-- Iteration preserves the literal composition of original strict maps. -/
@[simp] theorem loopTailIterateMap_comp {E F G : LoopPrespectrum.{u}}
    (f : E ⟶ F) (g : F ⟶ G) (i : ℕ) :
    loopTailIterateMap (f ≫ g) i = loopTailIterateMap f i ≫ loopTailIterateMap g i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    change loopTailFunctor.map (loopTailIterateMap (f ≫ g) i) = _
    rw [ih]
    exact loopTailFunctor.map_comp _ _

/-- The original stage maps form strict squares with the original stabilization transitions. -/
theorem loopTailIterateMap_transition {E F : LoopPrespectrum.{u}} (f : E ⟶ F) (i : ℕ) :
    loopTailIterateMap f i ≫ loopTailTransition F i =
      loopTailTransition E i ≫ loopTailIterateMap f (i + 1) :=
  stabilizationMap_naturality (loopTailIterateMap f i)

/-- The strict original tower map acts by the existing cylinder-preserving telescope map. -/
def loopTailReplacementMap {E F : LoopPrespectrum.{u}} (f : E ⟶ F) :
    loopTailReplacement E ⟶ loopTailReplacement F :=
  Telescope.map (loopTailIterate E) (loopTailTransition E)
    (loopTailIterate F) (loopTailTransition F) (loopTailIterateMap f)
    (loopTailIterateMap_transition f)

/-- Every original cylinder keeps its exact original height. -/
@[simp] theorem loopTailReplacementMap_cylinder {E F : LoopPrespectrum.{u}} (f : E ⟶ F)
    (k i : ℕ) (s : unitInterval) (x : (loopTailIterate E i).space k) :
    (loopTailReplacementMap f).map k
      (Telescope.cylinder (loopTailIterate E) (loopTailTransition E) k i (s, x)) =
      Telescope.cylinder (loopTailIterate F) (loopTailTransition F) k i
        (s, (loopTailIterateMap f i).map k x) := rfl

/-- The unchanged original stage inclusion commutes strictly with the replacement map. -/
@[reassoc (attr := simp)] theorem loopTailReplacementMap_inclusion
    {E F : LoopPrespectrum.{u}} (f : E ⟶ F) (i : ℕ) :
    Telescope.inclusion (loopTailIterate E) (loopTailTransition E) i ≫
        loopTailReplacementMap f =
      loopTailIterateMap f i ≫ Telescope.inclusion (loopTailIterate F) (loopTailTransition F) i :=
  Telescope.inclusion_map (loopTailIterate E) (loopTailTransition E)
    (loopTailIterate F) (loopTailTransition F) (loopTailIterateMap f)
    (loopTailIterateMap_transition f) i

/-- The replacement's actual identity map is the literal identity on its quotient cylinders. -/
@[simp] theorem loopTailReplacementMap_id (E : LoopPrespectrum.{u}) :
    loopTailReplacementMap (𝟙 E) = 𝟙 (loopTailReplacement E) := by
  apply Telescope.hom_ext
  intro k i s x
  change Telescope.cylinder (loopTailIterate E) (loopTailTransition E) k i
    (s, (loopTailIterateMap (𝟙 E) i).map k x) = _
  rw [loopTailIterateMap_id]
  rfl

/-- The replacement map preserves actual composition, with no reparametrization or homotopy. -/
@[simp] theorem loopTailReplacementMap_comp {E F G : LoopPrespectrum.{u}}
    (f : E ⟶ F) (g : F ⟶ G) :
    loopTailReplacementMap (f ≫ g) = loopTailReplacementMap f ≫ loopTailReplacementMap g := by
  apply Telescope.hom_ext
  intro k i s x
  change Telescope.cylinder (loopTailIterate G) (loopTailTransition G) k i
    (s, (loopTailIterateMap (f ≫ g) i).map k x) =
      Telescope.cylinder (loopTailIterate G) (loopTailTransition G) k i
        (s, (loopTailIterateMap g i).map k ((loopTailIterateMap f i).map k x))
  rw [loopTailIterateMap_comp]
  rfl

/-- The same original loop-tail replacement is a genuine strict endofunctor. -/
def loopTailReplacementFunctor : LoopPrespectrum.{u} ⥤ LoopPrespectrum.{u} where
  obj := loopTailReplacement
  map := loopTailReplacementMap
  map_id := loopTailReplacementMap_id
  map_comp := loopTailReplacementMap_comp

/-- The original initial inclusion commutes strictly with the actual replacement map. -/
@[reassoc] theorem loopTailReplacementInclusion_naturality
    {E F : LoopPrespectrum.{u}} (f : E ⟶ F) :
    loopTailReplacementInclusion E ≫ loopTailReplacementMap f =
      f ≫ loopTailReplacementInclusion F := loopTailReplacementMap_inclusion f 0

/-- The unit is exactly the existing initial-stage inclusion, as a strict natural transformation. -/
def loopTailReplacementUnit : 𝟭 LoopPrespectrum.{u} ⟶ loopTailReplacementFunctor where
  app := loopTailReplacementInclusion
  naturality _E _F f := (loopTailReplacementInclusion_naturality f).symm

end Quillen.LoopPrespectrum
