/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalParameterFullRestrictionTelescope
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterIteratedFullNull

/-! # The actual full-open map in the original selected-null telescope -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum Quillen.KTheory.Bass
universe u
namespace Quillen.PerfectComplexes.GlobalParameterCoefficient
variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))}
    (f : P ⟶ Q) [IsOpenImmersion f.left]

/-- Realization preserves the actual two-factor full-open Model map. -/
theorem parameterRestrictionMap_eq_fullMap :
    parameterRestrictionMap f = ParameterFullCurrentNull.fullMap f.left :=
  Functor.whiskerRight_comp _ _ _

/-- The original selected-null open map is the same entire quotient telescope map. -/
theorem parameterTelescopeRestriction_eq_iteratedOpen :
    parameterTelescopeRestriction f = ParameterFullCurrentNull.iteratedOpen f.left := by
  apply NatTrans.ext
  funext X
  apply Telescope.hom_ext
  intro n i t x
  change Telescope.cylinder
    (fun j => ((strictDiagramIterate squareFunctor j).obj (parameterDiagram P)).obj X)
    (fun j => (strictDiagramTransition squareFunctor
      (SchemeNaturalSeed.seed (ParameterLaurentTrack.ambientTrack P.left)) j).app X) n i
      (t, (((strictDiagramIterate squareFunctor i).map
        (parameterRestrictionMap f)).app X).map n x) =
    Telescope.cylinder
      (fun j => ((strictDiagramIterate squareFunctor j).obj (parameterDiagram P)).obj X)
      (fun j => (strictDiagramTransition squareFunctor
        (SchemeNaturalSeed.seed (ParameterLaurentTrack.ambientTrack P.left)) j).app X) n i
        (t, (((strictDiagramIterate squareFunctor i).map
          (ParameterFullCurrentNull.fullMap f.left)).app X).map n x)
  rw [parameterRestrictionMap_eq_fullMap]
  rfl

end Quillen.PerfectComplexes.GlobalParameterCoefficient
