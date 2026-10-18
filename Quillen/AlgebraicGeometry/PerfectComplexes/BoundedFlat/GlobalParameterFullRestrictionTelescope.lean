/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalParameterCoefficientTelescope
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalParameterCoefficientRestriction
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalFullOpenTelescope
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalLocalizationTelescopeMaps

/-! # The actual parameter full-open arrow on the original Bass telescope -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum Quillen.KTheory.Bass
universe u
namespace Quillen.PerfectComplexes.GlobalParameterCoefficient
open GlobalSectionChangeIndex
variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))}
    (f : P ⟶ Q) [IsOpenImmersion f.left]

/-- Realize the original full-open parameter restriction. -/
def parameterRestrictionMap : parameterDiagram Q ⟶ parameterDiagram P :=
  Functor.whiskerRight (parameterFullRestriction f) prespectrumFunctor

/-- The full-open parameter restriction preserves the same original Bass seed. -/
theorem parameterRestriction_seed :
    SchemeNaturalSeed.seed (ParameterLaurentTrack.ambientTrack Q.left) ≫
        (strictDiagramFunctor squareFunctor).map (parameterRestrictionMap f) =
      parameterRestrictionMap f ≫
        SchemeNaturalSeed.seed (ParameterLaurentTrack.ambientTrack P.left) := by
  apply SchemeNaturalSeed.seed_square
  have h := (ParameterLaurentTrack.changeWeak_equivariant f.left).comp
    (ParameterLaurentTrack.openRestriction_equivariant f.left)
  simpa only [parameterRestrictionMap, parameterFullRestriction,
    Functor.whiskerRight_comp] using h

/-- Original full-open restriction at each parameter Bass stage. -/
def parameterFiniteRestriction (i : ℕ) :
    (strictDiagramIterate squareFunctor i).obj (parameterDiagram Q) ⟶
      (strictDiagramIterate squareFunctor i).obj (parameterDiagram P) :=
  (strictDiagramIterate squareFunctor i).map (parameterRestrictionMap f)

/-- The original seed square gives every actual finite restriction transition. -/
theorem parameterFiniteRestriction_transition (i : ℕ) :
    parameterFiniteRestriction f i ≫ strictDiagramTransition squareFunctor
        (SchemeNaturalSeed.seed (ParameterLaurentTrack.ambientTrack P.left)) i =
      strictDiagramTransition squareFunctor
        (SchemeNaturalSeed.seed (ParameterLaurentTrack.ambientTrack Q.left)) i ≫
        parameterFiniteRestriction f (i + 1) :=
  (strictDiagramTransition_map squareFunctor
    (SchemeNaturalSeed.seed (ParameterLaurentTrack.ambientTrack Q.left))
    (SchemeNaturalSeed.seed (ParameterLaurentTrack.ambientTrack P.left))
    (parameterRestrictionMap f) (parameterRestriction_seed f) i).symm

/-- The complete original parameter telescope restricts to the actual open product telescope. -/
def parameterTelescopeRestriction : parameterTelescope Q.left ⟶ parameterTelescope P.left :=
  Telescope.diagramMap
    (fun i => (strictDiagramIterate squareFunctor i).obj (parameterDiagram Q))
    (fun i => (strictDiagramIterate squareFunctor i).obj (parameterDiagram P))
    (strictDiagramTransition squareFunctor
      (SchemeNaturalSeed.seed (ParameterLaurentTrack.ambientTrack Q.left)))
    (strictDiagramTransition squareFunctor
      (SchemeNaturalSeed.seed (ParameterLaurentTrack.ambientTrack P.left)))
    (parameterFiniteRestriction f) (parameterFiniteRestriction_transition f)

/-- The original global full-open factorization is the same actual Model arrow. -/
theorem globalFullRestriction_factor :
    openRowChangeWeak f ≫ globalOpenRestriction f = globalOpenFineRestriction f := by
  apply NatTrans.ext
  funext a
  apply Model.Hom.ext
  change (𝟭 _) ⋙ ((globalOpenFineRestriction f).app a).functor = _
  exact CategoryTheory.Functor.id_comp _

end Quillen.PerfectComplexes.GlobalParameterCoefficient
