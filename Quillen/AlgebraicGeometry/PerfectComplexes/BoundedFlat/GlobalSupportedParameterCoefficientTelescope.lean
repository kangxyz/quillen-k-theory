/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalSupportedParameterCoefficientSeed
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalLocalizationTelescopeStable
public import Quillen.KTheory.Bass.StrictDiagramIndexRowTelescope

/-!
# The actual supported integral Spec-row Bass telescope

The original supported seed square gives a natural isomorphism of entire iterated-seed
quotient telescopes. Its specified inverse comes from the actual index and Model row
isomorphisms. Composing with the existing supported restriction yields the stable comparison
to the unchanged original fine supported telescope.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open CommRingCat.PolynomialLaurent
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum Quillen.KTheory.Bass
universe u
namespace Quillen.PerfectComplexes.GlobalSupportedParameterCoefficient
open GlobalSectionChangeIndex

/-- The original supported parameter telescope with its actual scalar/null seed. -/
def parameterTelescope {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f] :
    Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{u + 1} :=
  StrictDiagramIndexChange.telescope squareFunctor
    (SchemeNaturalSeed.seed (ParameterLaurentTrack.supportedTrack f))

variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q)
    [IsOpenImmersion f.left]

/-- The complete actual supported Model row isomorphism on original prespectra. -/
def rowSpectrumIso : specUnder ⋙ parameterDiagram f ≅ supportedRow f ⋙ prespectrumFunctor :=
  Functor.isoWhiskerRight (parameterSupportedRowIso f) prespectrumFunctor

/-- The original supported seed supplies the exact index-plus-row transition square. -/
theorem seed_square_row :
    Functor.whiskerLeft specUnder
        (SchemeNaturalSeed.seed (ParameterLaurentTrack.supportedTrack f.left)) ≫
      (StrictDiagramIndexChange.iso specUnder _ squareFunctor specSquare
        (parameterDiagram f)).hom ≫
      (strictDiagramFunctor (laurentUnderSquareFunctor _)).map (rowSpectrumIso f).hom =
        (rowSpectrumIso f).hom ≫ (supportedLaurentAction f).track.seed := by
  exact seed_square f

/-- Every finite supported comparison is the original index iso and iterated Model row iso. -/
def finiteIso (i : ℕ) :
    specUnder ⋙ (strictDiagramIterate squareFunctor i).obj (parameterDiagram f) ≅
      SupportedTelescope.globalDiagram f i :=
  StrictDiagramIndexRow.finiteIso specUnder _ squareFunctor specSquare (rowSpectrumIso f) i

/-- The entire supported parameter telescope is the original supported global coefficient tower. -/
def telescopeIso : specUnder ⋙ parameterTelescope f.left ≅ SupportedTelescope.globalTelescope f :=
  StrictDiagramIndexRow.telescopeIso specUnder _ squareFunctor specSquare (rowSpectrumIso f)
    (SchemeNaturalSeed.seed (ParameterLaurentTrack.supportedTrack f.left))
    (supportedLaurentAction f).track.seed (seed_square_row f)

/-- The actual supported Spec-row comparison has its specified stable inverse. -/
theorem telescopeIso_stable (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    IsStableEquivalence ((telescopeIso f).hom.app a) := by
  intro d
  infer_instance

/-- Actual Spec restriction followed by the original fine supported coefficient restriction. -/
def fineTelescopeComparison :
    specUnder ⋙ parameterTelescope f.left ⟶ boundedFlatCoefficientSupportedBassTelescopeFunctor f :=
  (telescopeIso f).hom ≫ SupportedTelescope.telescopeRestriction f

/-- The complete comparison to the original fine supported telescope is stable at each algebra. -/
theorem fineTelescopeComparison_stable (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    IsStableEquivalence ((fineTelescopeComparison f).app a) :=
  (telescopeIso_stable f a).comp (SupportedTelescope.telescopeRestriction_isStableEquivalence f a)

end Quillen.PerfectComplexes.GlobalSupportedParameterCoefficient
