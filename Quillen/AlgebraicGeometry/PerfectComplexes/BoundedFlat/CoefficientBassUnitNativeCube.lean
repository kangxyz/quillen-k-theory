/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassUnitScalarCube
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassUnitNativeFaces
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassUnitInteriorCube

/-! The concrete original native six-faced Bass identity cube, with point and structure laws. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassUnitNativeCube
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable (a : Under R)
open CoefficientBassUnitNodes CoefficientBassUnitNativeFaces CoefficientBassUnitScalarCube

/-- The pure scalar cube acts on every original input and level through one actual native family. -/
def cubeLevel (n : ℕ) :
    C(unitInterval × (unitInterval × (unitInterval ×
      (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n)),
      (originalPrespectrum (boundedFlatPerfectWaldhausen
        (space (op P, (laurentUnderFunctor R).obj a)))).space n) :=
  ⟨fun z ↦ prespectrumSimplexFamily (simplex P a) n
    (scalarCube.{u} ![z.1, z.2.1, z.2.2.1], z.2.2.2), by fun_prop⟩

/-- Equal scalar parameters give equal values in the unchanged native simplex family. -/
theorem family_parameter_congr {V W : Model.{u}} {k : ℕ}
    (S : ModelSimplex V W k) (n : ℕ)
    (z w : StdSimplex ℝ (Fin (k + 1))) (h : z = w) (x : (prespectrum V).space n) :
    prespectrumSimplexFamily S n (z, x) = prespectrumSimplexFamily S n (w, x) :=
  congrArg (fun v ↦ prespectrumSimplexFamily S n (v, x)) h

/-- The actual original SquareCylinder, constructed only after all twelve whole scalar joins. -/
def interiorCube : BoundedFlatCoefficientBassIdentityInteriorCube P a where
  level := cubeLevel P a
  at_zero n s t x :=
    (family_parameter_congr (simplex P a) n _ _ (cube_zero.{u} s t) x).trans
      (h0_native P a n s t x)
  at_one n s t x :=
    (family_parameter_congr (simplex P a) n _ _ (cube_one.{u} s t) x).trans
      (identity_native P a n s t x)
  bottom n r t x :=
    (family_parameter_congr (simplex P a) n _ _ (cube_bottom.{u} r t) x).trans
      (bottom_native P a n r t x)
  top n r t x :=
    (family_parameter_congr (simplex P a) n _ _ (cube_top.{u} r t) x).trans
      (top_native P a n r t x)
  left n r s x :=
    (family_parameter_congr (simplex P a) n _ _ (cube_left.{u} r s) x).trans
      (plus_native P a n r s x)
  right n r s x :=
    (family_parameter_congr (simplex P a) n _ _ (cube_right.{u} r s) x).trans
      (minus_native P a n r s x)
  at_point n r s t := family_point P a n (scalarCube.{u} ![r, s, t])
  comm n r s t x z := family_structure P a n (scalarCube.{u} ![r, s, t]) x z

/-- The entire native cube has this literal value, with all three coordinates independent. -/
theorem interiorCube_level (n : ℕ) (r s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    (interiorCube P a).level n (r, (s, (t, x))) =
      prespectrumSimplexFamily (simplex P a) n (scalarCube.{u} ![r, s, t], x) := rfl

/-- The same actual level-zero source and value are retained, with no replacement zero object. -/
theorem interiorCube_level_zero (r s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space 0) :
    (interiorCube P a).level 0 (r, (s, (t, x))) =
      prespectrumSimplexFamily (simplex P a) 0 (scalarCube.{u} ![r, s, t], x) := rfl

end Quillen.PerfectComplexes.CoefficientBassUnitNativeCube
