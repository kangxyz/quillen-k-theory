/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerve
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeNativeCube

/-! The original chosen whole Bass composition cube survives exact common-reference lifting. -/
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.PerfectComplexes Quillen.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open scoped Topology unitInterval
universe u
namespace QuillenTest.CommonReferenceNerveMWhole
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- No replacement scalar cube, vertex order, native input, or parameter is used. -/
theorem original_chosen_whole_cube (n : ℕ) (r s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    CommonReferenceNerve.prespectrumFamily (BassOverlap.commonReference P u v)
        (BassMWhole.nodes P u v) n (BassMWhole.scalarCube.{u} ![r, s, t], x) =
      (BassMWhole.interiorCube P u v).level n (r, (s, (t, x))) := by
  rw [CommonReferenceNerve.prespectrumFamily_eq]
  exact (BassMWhole.interiorCube_level P u v n r s t x).symm

/-- The same chosen cube survives at the original level-zero input, with no positive-level cut. -/
theorem original_chosen_whole_cube_level_zero (r s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space 0) :
    CommonReferenceNerve.prespectrumFamily (BassOverlap.commonReference P u v)
        (BassMWhole.nodes P u v) 0 (BassMWhole.scalarCube.{u} ![r, s, t], x) =
      (BassMWhole.interiorCube P u v).level 0 (r, (s, (t, x))) :=
  original_chosen_whole_cube P u v 0 r s t x

end QuillenTest.CommonReferenceNerveMWhole
