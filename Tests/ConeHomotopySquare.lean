/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Topology.Prespectrum.ConeHomotopySquare

/-!
Semantic consumers for actual homotopy-square cone maps: original target points, independent
cone/structure parameters, and retention of the supplied square track after parameter looping.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Quillen Quillen.LoopPrespectrum
open scoped Topology unitInterval

universe u

namespace ConeHomotopySquareConsumers

variable {E F E' F' : LoopPrespectrum.{u}}
  (f : E ⟶ F) (g : E' ⟶ F') (a : E ⟶ E') (b : F ⟶ F')
  (H : Homotopy (f ≫ b) (a ≫ g))

/-- The unchanged target point is sent by the original target arrow before cone inclusion. -/
theorem original_target_points (n : ℕ) (y : F.space n) :
    (mappingConeSquareMap f g a b H).map n ((mappingConeInclusion f).map n y) =
      (mappingConeInclusion g).map n (b.map n y) :=
  congrArg (fun h ↦ h.map n y) (mappingConeSquareMap_inclusion f g a b H)

/-- Cone time and structure time remain independent in the actual constructed map. -/
theorem independent_cone_structure_parameters (n : ℕ) (s t : unitInterval) (x : E.space n) :
    (mappingConeSquareMap f g a b H).map (n + 1)
        (ReducedMappingCone.cylinder (E.point (n + 1)) (F.point (n + 1)) (f.map (n + 1))
          (s, E.structureMap n x t)) =
      (mappingCone g).structureMap n
        ((mappingConeSquareMap f g a b H).map n
          (ReducedMappingCone.cylinder (E.point n) (F.point n) (f.map n) (s, x))) t :=
  congrArg (fun p ↦ p t) ((mappingConeSquareMap f g a b H).comm n
    (ReducedMappingCone.cylinder (E.point n) (F.point n) (f.map n) (s, x)))

/-- Looping the actual map retains the whole square track at any specified loop coordinate. -/
theorem parameter_loop_retains_square_track (n : ℕ) (s t : unitInterval) (x : E.space n)
    (γ : Path ((mappingCone f).point n) ((mappingCone f).point n))
    (hγ : γ s = ReducedMappingCone.cylinder (E.point n) (F.point n) (f.map n)
      (⟨(t : ℝ) / 2, by constructor <;> linarith [t.2.1, t.2.2]⟩, x)) :
    Path.toContinuousMap ((parameterLoopingMap (mappingConeSquareMap f g a b H)).map n γ) s =
      (mappingConeInclusion g).map n (H.level n (t, x)) := by
  change (mappingConeSquareMap f g a b H).map n (γ s) = _
  rw [hγ]
  exact mappingConeSquareMap_first_half f g a b H n t x

/-- The midpoint is the original target of the source image, where the two tracks join. -/
theorem original_midpoint (n : ℕ) (x : E.space n) :
    (mappingConeSquareMap f g a b H).map n
      (ReducedMappingCone.cylinder (E.point n) (F.point n) (f.map n)
        (⟨(1 : ℝ) / 2, by constructor <;> norm_num⟩, x)) =
      (mappingConeInclusion g).map n (g.map n (a.map n x)) := by
  have hh := mappingConeSquareMap_first_half f g a b H n 1 x
  rw [H.at_one] at hh
  exact hh

end ConeHomotopySquareConsumers
