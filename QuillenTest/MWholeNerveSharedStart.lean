/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeNerveSharedStart

/-! The complete two-parameter initial faces of the original fixed outer cubes agree as maps. -/
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.PerfectComplexes Quillen.Waldhausen.IteratedS
open scoped Topology unitInterval
universe u
namespace QuillenTest.MWholeNerveSharedStart
open BassMWholeNerve
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  {a b c d : Under R} (u : a ⟶ b) (v : b ⟶ c) (w : c ⟶ d)

/-- Restricting the two actual cube lifts gives equal continuous whole-face maps. -/
theorem original_whole_start_maps :
    (cubeLift P (u ≫ v) w (BassH0Diagram.reference P ((u ≫ v) ≫ w))
      (h0Anchor P (u ≫ v) w)).comp
        (⟨fun z : unitInterval × unitInterval ↦ ![0, z.1, z.2], by fun_prop⟩) =
    (cubeLift P u (v ≫ w) (BassH0Diagram.reference P ((u ≫ v) ≫ w))
      (rightStartingAnchor P u v w)).comp
        (⟨fun z : unitInterval × unitInterval ↦ ![0, z.1, z.2], by fun_prop⟩) := by
  ext z
  exact fixed_outer_cubes_shared_start P u v w z.1 z.2

end QuillenTest.MWholeNerveSharedStart
