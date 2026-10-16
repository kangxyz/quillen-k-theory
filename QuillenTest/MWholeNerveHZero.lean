/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeNerveHZero

/-! Whole original H0 parameter equality and level-zero native preservation of the selected cube. -/
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.PerfectComplexes Quillen.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open scoped Topology unitInterval
universe u
namespace QuillenTest.MWholeNerveHZero
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- Equality holds at every original H0 point in the actual nerve, before native evaluation. -/
theorem entire_original_starting_face (s t : unitInterval) :
    BassMWholeNerve.cubeLift P u v (BassH0Diagram.reference P (u ≫ v))
        (BassMWholeNerve.h0Anchor P u v) ![0, s, t] =
      CommonReferenceNerve.parameter (BassH0Diagram.reference P (u ≫ v))
        (BassH0Diagram.nodes P (u ≫ v)) (BassH0Diagram.parameter (s, t)) :=
  BassMWholeNerve.cubeLift_original_h0 P u v s t

/-- The selected whole scalar cube and original level-zero input survive the same reanchoring. -/
theorem original_whole_cube_level_zero (r s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space 0) :
    CommonReferenceNerve.prespectrumFamily (BassH0Diagram.reference P (u ≫ v))
        (ModelSimplex.reanchorNodes (BassMWholeNerve.h0Anchor P u v) (BassMWhole.nodes P u v)) 0
        (BassMWhole.scalarCube.{u} ![r, s, t], x) =
      (BassMWhole.interiorCube P u v).level 0 (r, (s, (t, x))) :=
  BassMWholeNerve.reanchored_native_cube P u v _ (BassMWholeNerve.h0Anchor P u v) 0 r s t x

end QuillenTest.MWholeNerveHZero
