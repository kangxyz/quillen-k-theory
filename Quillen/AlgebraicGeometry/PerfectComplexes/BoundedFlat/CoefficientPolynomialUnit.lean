/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.OriginalUnitSquare
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassConditionalLaws

/-! A native producer of the exact original coefficient polynomial identity square. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Quillen.LoopPrespectrum
open Quillen.PolynomialBaseChange Quillen.Scheme.CoefficientBaseChange
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} (P : Over (Spec R))

/-- The actual original polynomial square has both original geometric unit tracks as its sides. -/
def boundedFlatCoefficientPolynomialIdentitySquare (a : Under R) :
    BoundedFlatCoefficientPolynomialIdentitySquare P a := by
  let S := boundedFlatPerfectPrespectrumUnitSquare (polynomialProjection P a)
  refine S.ofBoundaryLevels _ _ _ _ ?_ (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl)
  intro n
  have transport {X Y : Scheme.{u}} (f : X ⟶ Y) (p : X ⟶ X) (w : Y ⟶ Y)
      (ep : p = 𝟙 X) (ew : w = 𝟙 Y) (h : p ≫ f = f ≫ w) :
      (boundedFlatPerfectPrespectrumSquareHomotopy p f f w h).level n =
        (boundedFlatPerfectPrespectrumSquareHomotopy (𝟙 X) f f (𝟙 Y) (by simp)).level n := by
    subst p
    subst w
    rfl
  exact transport (polynomialProjection P a) _ _
    ((congrArg (coefficientMap P) ((polynomialUnderFunctor R).map_id a)).trans
      (boundedFlatCoefficientGeometricIdentity P ((polynomialUnderFunctor R).obj a)))
    (boundedFlatCoefficientGeometricIdentity P a) _

end Quillen.PerfectComplexes
