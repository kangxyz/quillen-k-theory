/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeScalarCube
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassInteriorCube

/-! The concrete original native six-faced Bass interior cube, with point and structure laws. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity
open Quillen.PolynomialBaseChange Quillen.Scheme.CoefficientBaseChange
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassMWhole
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- The pure scalar cube acts on every original input and level through one actual native family. -/
def cubeLevel (n : ℕ) :
    C(unitInterval × (unitInterval × (unitInterval ×
      (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n)),
      (originalPrespectrum (boundedFlatPerfectWaldhausen
        (space (op P, (laurentUnderFunctor R).obj c)))).space n) :=
  ⟨fun z ↦ prespectrumSimplexFamily (simplex P u v) n
    (scalarCube.{u} ![z.1, z.2.1, z.2.2.1], z.2.2.2), by fun_prop⟩

/-- The actual original SquareCylinder, constructed only after all twelve whole scalar joins. -/
def interiorCube : BoundedFlatCoefficientBassCompositionInteriorCube P u v where
  level := cubeLevel P u v
  at_zero n s t x := by
    change prespectrumSimplexFamily (simplex P u v) n (scalarCube.{u} ![0, s, t], x) = _
    rw [cube_zero]
    exact h0_native P u v n s t x
  at_one n s t x := by
    change prespectrumSimplexFamily (simplex P u v) n (scalarCube.{u} ![1, s, t], x) = _
    rw [cube_one]
    exact h1_native P u v n s t x
  bottom n r t x := by
    change prespectrumSimplexFamily (simplex P u v) n (scalarCube.{u} ![r, 0, t], x) = _
    rw [cube_bottom]
    exact bottom_native P u v n r t x
  top n r t x := by
    change prespectrumSimplexFamily (simplex P u v) n (scalarCube.{u} ![r, 1, t], x) = _
    rw [cube_top]
    exact m_native P u v n r t x
  left n r s x := by
    change prespectrumSimplexFamily (simplex P u v) n (scalarCube.{u} ![r, s, 0], x) = _
    rw [cube_left]
    exact plus_native P u v n r s x
  right n r s x := by
    change prespectrumSimplexFamily (simplex P u v) n (scalarCube.{u} ![r, s, 1], x) = _
    rw [cube_right]
    exact minus_native P u v n r s x
  at_point n r s t := family_point P u v n _
  comm n r s t x z := family_structure P u v n _ x z

/-- The entire native cube has this literal value, with all three coordinates independent. -/
theorem interiorCube_level (n : ℕ) (r s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    (interiorCube P u v).level n (r, (s, (t, x))) =
      prespectrumSimplexFamily (simplex P u v) n (scalarCube.{u} ![r, s, t], x) := rfl

/-- The same actual level-zero source and value are retained, with no replacement zero object. -/
theorem interiorCube_level_zero (r s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space 0) :
    (interiorCube P u v).level 0 (r, (s, (t, x))) =
      prespectrumSimplexFamily (simplex P u v) 0 (scalarCube.{u} ![r, s, t], x) := rfl

end Quillen.PerfectComplexes.BassMWhole
