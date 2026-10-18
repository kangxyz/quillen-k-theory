/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalParameterCoefficientSeedCompatibility
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalSectionTelescope
public import Quillen.KTheory.Bass.StrictDiagramIndexRowTelescope

/-! # The original parameter Bass telescope on the integral Spec row -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open CommRingCat.PolynomialLaurent
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum Quillen.KTheory.Bass
universe u
namespace Quillen.PerfectComplexes.GlobalParameterCoefficient
open GlobalSectionChangeIndex

/-- The actual parameter telescope uses only the original scalar/null seed. -/
def parameterTelescope (Q : Scheme.{u}) : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{u + 1} :=
  StrictDiagramIndexChange.telescope squareFunctor
    (SchemeNaturalSeed.seed (ParameterLaurentTrack.ambientTrack Q))

/-- Realize the original full Model row isomorphism. -/
def rowSpectrumIso (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))) :
    specUnder ⋙ parameterDiagram Q ≅ globalRow Q ⋙ prespectrumFunctor :=
  Functor.isoWhiskerRight (parameterRowModelIso Q) prespectrumFunctor

/-- The actual original seed supplies the sole transition input of index-plus-row descent. -/
theorem seed_square_row (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))) :
    Functor.whiskerLeft specUnder
        (SchemeNaturalSeed.seed (ParameterLaurentTrack.ambientTrack Q.left)) ≫
      (StrictDiagramIndexChange.iso specUnder _ squareFunctor specSquare
        (parameterDiagram Q)).hom ≫
      (strictDiagramFunctor (laurentUnderSquareFunctor _)).map (rowSpectrumIso Q).hom =
        (rowSpectrumIso Q).hom ≫ (globalLaurentAction Q).track.seed := by
  exact seed_square Q

/-- Every finite stage is the actual index comparison followed by the iterated Model row iso. -/
def finiteIso (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))) (i : ℕ) :
    specUnder ⋙ (strictDiagramIterate squareFunctor i).obj (parameterDiagram Q) ≅
      globalDiagram Q i :=
  StrictDiagramIndexRow.finiteIso specUnder _ squareFunctor specSquare (rowSpectrumIso Q) i

/-- The entire original parameter telescope restricts to the original global coefficient tower. -/
def telescopeIso (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))) :
    specUnder ⋙ parameterTelescope Q.left ≅ globalTelescope Q :=
  StrictDiagramIndexRow.telescopeIso specUnder _ squareFunctor specSquare (rowSpectrumIso Q)
    (SchemeNaturalSeed.seed (ParameterLaurentTrack.ambientTrack Q.left))
    (globalLaurentAction Q).track.seed (seed_square_row Q)

/-- The actual Spec-row telescope comparison is stable because it has the displayed inverse. -/
theorem telescopeIso_stable (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    IsStableEquivalence ((telescopeIso Q).hom.app a) := by
  intro d
  infer_instance

end Quillen.PerfectComplexes.GlobalParameterCoefficient
