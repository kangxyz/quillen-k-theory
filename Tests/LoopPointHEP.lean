/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
import Quillen.Topology.Prespectrum.ParameterLoopingPointHEP
import Quillen.Waldhausen.SConstruction.Iterated.PointHEP

/-!
# Original constant-loop point HEP consumers

The actual double-loop basepoint retains HEP with no new hypothesis. The
unchanged original S-spectrum, including its degree-zero loop space, remains
well-based after parameter looping. These are actual point inclusions, not
replacement CW models or a separation-only criterion.
-/

open CategoryTheory
open Quillen Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS

namespace Quillen.Tests.LoopPointHEP

universe u v

/-- The real point-HEP construction iterates on the original compact-open loop topology. -/
theorem double_loop_point_homotopyExtensionProperty
    {X : Type u} [TopologicalSpace X] (x : X) (hx : IsClosed ({x} : Set X))
    (h : Quillen.homotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} x))) :
    Quillen.homotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (Path.refl (Path.refl x)))) :=
  path_refl_homotopyExtensionProperty (isClosed_singleton_refl hx)
    (path_refl_homotopyExtensionProperty hx h)

/-- Actual original S-level points retain HEP after parameter looping, also at degree zero. -/
theorem original_s_parameterLooping_point_homotopyExtensionProperty
    {C : Type u} [Category.{v} C] (W : Waldhausen.Structure C) (n : ℕ) :
    Quillen.homotopyExtensionProperty (TopCat.ofHom
      (ContinuousMap.const PUnit.{max u v + 1}
        ((parameterLooping (originalPrespectrum W)).point n))) :=
  parameterLooping_point_homotopyExtensionProperty _ n isClosed_singleton
    (originalPrespectrum_point_homotopyExtensionProperty W n)

/-- Nonzero output height makes the entire deformed original loop constant. -/
theorem actual_minimum_controls_whole_loop
    {X : Type u} [TopologicalSpace X] (x : X) (R : PointCylinderRetraction x)
    (t : unitInterval) (γ : Path x x) (h : R.loopHeight (t, γ) ≠ 0) :
    ∀ s : unitInterval, R.loopPath (t, γ) s = x := by
  rw [R.loopPath_eq_refl_of_loopHeight_ne_zero (t, γ) h]
  intro s
  rfl

end Quillen.Tests.LoopPointHEP
