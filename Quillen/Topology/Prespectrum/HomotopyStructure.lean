/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Topology.Prespectrum.Looping

/-!
# The original structure map on all finite homotopy sets

Compose the actual adjoint structure map with the genuine inverse loop-degree shift, including
outer degree zero. Naturality retains the original spectrum map. For the untransposed loop-tail
construction, the return loop shift gives the next original structure map without a coordinate
swap. No Omega or connectivity assumption is used.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory

universe u

namespace Quillen.LoopPrespectrum

/-- The original structure-induced function, including the zeroth outer homotopy set. -/
def structureHomotopyMap (E : LoopPrespectrum.{u}) (k n : ℕ) :
    HomotopyGroup.Pi n (E.space k) (E.point k) →
      HomotopyGroup.Pi (n + 1) (E.space (k + 1)) (E.point (k + 1)) :=
  (loopShiftEquiv n).symm ∘ homotopyGroupMap (E.structureMap k) (E.map_point k)

/-- The original structure-induced functions commute with the actual spectrum morphism. -/
theorem structureHomotopyMap_naturality {E F : LoopPrespectrum.{u}} (f : E ⟶ F) (k n : ℕ)
    (a : HomotopyGroup.Pi n (E.space k) (E.point k)) :
    structureHomotopyMap F k n (homotopyGroupMap (f.map k) (f.map_point k) a) =
      homotopyGroupMap (f.map (k + 1)) (f.map_point (k + 1)) (structureHomotopyMap E k n a) := by
  induction a using Quotient.inductionOn with
  | h p =>
    apply congrArg Quotient.mk'
    ext z
    exact (congrArg (fun γ ↦ γ (z 0)) (f.comm k (p (Fin.tail z)))).symm

/-- In the untransposed loop-tail structure, returning by the genuine loop shift is followed
by precisely the next original structure map on finite homotopy sets. -/
theorem structureHomotopyMap_looping_tail (E : LoopPrespectrum.{u}) (k n : ℕ)
    (a : HomotopyGroup.Pi (n + 1) (E.space (k + 1)) (E.point (k + 1))) :
    structureHomotopyMap (looping (tail E)) k n (loopShiftEquiv n a) =
      homotopyGroupMap (E.structureMap (k + 1)) (E.map_point (k + 1)) a := by
  apply (loopShiftEquiv (x := Path.refl (E.point (k + 1 + 1))) n).injective
  change loopShiftEquiv n ((loopShiftEquiv n).symm
    (homotopyGroupMap (basedLoopMap (E.structureMap (k + 1)) (E.map_point (k + 1)))
      (basedLoopMap_refl _ _) (loopShiftEquiv n a))) = _
  rw [Equiv.apply_symm_apply]
  exact (loopShiftEquiv_natural n (E.structureMap (k + 1)) (E.map_point (k + 1)) a).symm

end Quillen.LoopPrespectrum
