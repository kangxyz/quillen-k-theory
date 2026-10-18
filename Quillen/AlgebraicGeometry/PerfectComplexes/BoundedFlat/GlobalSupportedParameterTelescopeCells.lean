/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalSupportedParameterCoefficientTelescope

/-! # Exact stage and height formulas for the actual supported parameter comparisons -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum Quillen.KTheory.Bass
universe u
namespace Quillen.PerfectComplexes.GlobalSupportedParameterCoefficient
open GlobalSectionChangeIndex
variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))}
    (f : P ⟶ Q) [IsOpenImmersion f.left]

/-- The actual row isomorphism retains every stage and the independent telescope height. -/
theorem telescopeIso_cylinder (a : Under (CommRingCat.of (ULift.{u} ℤ)))
    (n i : ℕ) (t : unitInterval)
    (x : ((strictDiagramIterate squareFunctor i).obj (parameterDiagram f)).obj
      (specUnder.obj a) |>.space n) :
    ((telescopeIso f).hom.app a).map n
      (Telescope.cylinder
        (fun j => ((strictDiagramIterate squareFunctor j).obj (parameterDiagram f)).obj
          (specUnder.obj a))
        (fun j => (strictDiagramTransition squareFunctor
          (SchemeNaturalSeed.seed (ParameterLaurentTrack.supportedTrack f.left)) j).app
          (specUnder.obj a)) n i (t, x)) =
      Telescope.cylinder (fun j => (SupportedTelescope.globalDiagram f j).obj a)
        (fun j => (SupportedTelescope.globalTransition f j).app a) n i
        (t, ((finiteIso f i).hom.app a).map n x) := rfl

/-- The inverse isomorphism preserves the same original quotient coordinate. -/
theorem telescopeIso_inv_cylinder (a : Under (CommRingCat.of (ULift.{u} ℤ)))
    (n i : ℕ) (t : unitInterval) (x : ((SupportedTelescope.globalDiagram f i).obj a).space n) :
    ((telescopeIso f).inv.app a).map n
      (Telescope.cylinder (fun j => (SupportedTelescope.globalDiagram f j).obj a)
        (fun j => (SupportedTelescope.globalTransition f j).app a) n i (t, x)) =
      Telescope.cylinder
        (fun j => ((strictDiagramIterate squareFunctor j).obj (parameterDiagram f)).obj
          (specUnder.obj a))
        (fun j => (strictDiagramTransition squareFunctor
          (SchemeNaturalSeed.seed (ParameterLaurentTrack.supportedTrack f.left)) j).app
          (specUnder.obj a)) n i (t, ((finiteIso f i).inv.app a).map n x) := rfl

end Quillen.PerfectComplexes.GlobalSupportedParameterCoefficient
