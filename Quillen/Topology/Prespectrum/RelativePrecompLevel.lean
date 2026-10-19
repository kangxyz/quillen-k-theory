/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Topology.Prespectrum.RelativeHomotopyWhiskering

/-!
# Whole-level evaluation of a precomposed relative homotopy

The continuous parameter map keeps the two original times independent and applies the
specified prespectrum map only to the space coordinate. The level formula is stated after
forgetting relative endpoint evidence, before specializing geometric constructions.
-/
@[expose] public section
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Quillen.LoopPrespectrum.Homotopy.RelHomotopy
variable {D E F : LoopPrespectrum.{u}}

/-- Precomposition changes only the space coordinate in the two-time parameter domain. -/
def precompParameter (h : D ⟶ E) (n : ℕ) :
    C(unitInterval × (unitInterval × D.space n), unitInterval × (unitInterval × E.space n)) :=
  ⟨fun z => (z.1, (z.2.1, h.map n z.2.2)), by fun_prop⟩

/-- The original precomposition formula as an equality of complete continuous level maps. -/
theorem precomp_level_toContinuousMap {f g : E ⟶ F} {H K : Homotopy f g}
    (h : D ⟶ E) (N : H.RelHomotopy K) (n : ℕ) :
    ((precomp h N).level n).toContinuousMap =
      (N.level n).toContinuousMap.comp (precompParameter h n) := rfl

end Quillen.LoopPrespectrum.Homotopy.RelHomotopy
