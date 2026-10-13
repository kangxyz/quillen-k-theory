/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Prespectrum.Looping

/-!
# Strict functoriality of the original loop-tail construction

Dropping the initial level acts on the original strict prespectrum maps. Composing this actual
tail functor with the existing untransposed looping functor gives the loop-tail functor. The
unchanged original stabilization maps form a strict natural transformation from the identity.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory
open scoped Topology unitInterval

universe u

namespace Quillen.LoopPrespectrum

/-- Drop the initial level of an original strict prespectrum map. -/
def tailMap {E F : LoopPrespectrum.{u}} (f : E ⟶ F) : tail E ⟶ tail F where
  map n := f.map (n + 1)
  map_point n := f.map_point (n + 1)
  comm n x := f.comm (n + 1) x

/-- The original tail construction is an actual strict functor. -/
def tailFunctor : LoopPrespectrum.{u} ⥤ LoopPrespectrum.{u} where
  obj := tail
  map := tailMap
  map_id _E := by apply Hom.ext; funext n; rfl
  map_comp _f _g := by apply Hom.ext; funext n; rfl

/-- The existing untransposed looping functor applied to the original tail. -/
def loopTailFunctor : LoopPrespectrum.{u} ⥤ LoopPrespectrum.{u} :=
  tailFunctor ⋙ loopingFunctor

/-- Each loop coordinate is postcomposed with the unchanged original next-level map. -/
@[simp] theorem loopTailFunctor_map_apply {E F : LoopPrespectrum.{u}} (f : E ⟶ F)
    (n : ℕ) (γ : Path (E.point (n + 1)) (E.point (n + 1))) (t : unitInterval) :
    Path.toContinuousMap ((loopTailFunctor.map f).map n γ) t = f.map (n + 1) (γ t) := rfl

/-- The original structure maps are natural with respect to every original strict map. -/
theorem stabilizationMap_naturality {E F : LoopPrespectrum.{u}} (f : E ⟶ F) :
    f ≫ stabilizationMap F = stabilizationMap E ≫ loopTailFunctor.map f := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  exact (f.comm n x).symm

/-- The unchanged stabilization map is the component of a strict natural transformation. -/
def stabilizationNatTrans : 𝟭 LoopPrespectrum.{u} ⟶ loopTailFunctor where
  app := stabilizationMap
  naturality _E _F f := stabilizationMap_naturality f

end Quillen.LoopPrespectrum
