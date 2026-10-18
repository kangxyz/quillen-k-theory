/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalParameterFullRestrictionSquare

/-! # Exact stage and height formulas for the actual parameter comparisons -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum Quillen.KTheory.Bass
universe u
namespace Quillen.PerfectComplexes.GlobalParameterCoefficient
open GlobalSectionChangeIndex
variable (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))

/-- The actual row isomorphism retains every stage and the independent telescope height. -/
theorem telescopeIso_cylinder (a : Under (CommRingCat.of (ULift.{u} ℤ)))
    (n i : ℕ) (t : unitInterval)
    (x : ((strictDiagramIterate squareFunctor i).obj (parameterDiagram Q)).obj
      (specUnder.obj a) |>.space n) :
    ((telescopeIso Q).hom.app a).map n
      (Telescope.cylinder
        (fun j => ((strictDiagramIterate squareFunctor j).obj (parameterDiagram Q)).obj
          (specUnder.obj a))
        (fun j => (strictDiagramTransition squareFunctor
          (SchemeNaturalSeed.seed (ParameterLaurentTrack.ambientTrack Q.left)) j).app
          (specUnder.obj a)) n i (t, x)) =
      Telescope.cylinder (fun j => (globalDiagram Q j).obj a)
        (fun j => (globalTransition Q j).app a) n i
        (t, ((finiteIso Q i).hom.app a).map n x) := rfl

/-- The inverse isomorphism preserves the same original quotient coordinate. -/
theorem telescopeIso_inv_cylinder (a : Under (CommRingCat.of (ULift.{u} ℤ)))
    (n i : ℕ) (t : unitInterval) (x : ((globalDiagram Q i).obj a).space n) :
    ((telescopeIso Q).inv.app a).map n
      (Telescope.cylinder (fun j => (globalDiagram Q j).obj a)
        (fun j => (globalTransition Q j).app a) n i (t, x)) =
      Telescope.cylinder
        (fun j => ((strictDiagramIterate squareFunctor j).obj (parameterDiagram Q)).obj
          (specUnder.obj a))
        (fun j => (strictDiagramTransition squareFunctor
          (SchemeNaturalSeed.seed (ParameterLaurentTrack.ambientTrack Q.left)) j).app
          (specUnder.obj a)) n i (t, ((finiteIso Q i).inv.app a).map n x) := rfl

end Quillen.PerfectComplexes.GlobalParameterCoefficient
