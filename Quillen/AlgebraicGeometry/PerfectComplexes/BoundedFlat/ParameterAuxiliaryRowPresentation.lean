/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterTensorRowPresentation
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterAuxiliaryTelescopeNull
public import Quillen.KTheory.Bass.SchemeModelRowPresentationInput

/-! # The actual auxiliary-support diagram of independent tensor-row presentations

The three supported Models and both original exact Model transformations are retained.
Original Laurent-unit preservation supplies the actual maps of presentations.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.LoopPrespectrum Quillen.KTheory.Bass
open Quillen.PerfectComplexes.ParameterLaurentTrack
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u
namespace Quillen.PerfectComplexes.GlobalSectionChangeIndex.ParameterAuxiliarySupport
variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f] (T : Q.Opens)

/-- Union support gives the genuine auxiliary fiber presentation. -/
def fiberPresentation (X : Scheme.{u}ᵒᵖ) :=
  ParameterTensorRowPresentation.supported (unionOpen f T).ι X

/-- The original auxiliary support gives the middle presentation. -/
def ambientPresentation (X : Scheme.{u}ᵒᵖ) :=
  ParameterTensorRowPresentation.supported T.ι X

/-- The inverse-image support gives the actual open presentation. -/
def openPresentation (X : Scheme.{u}ᵒᵖ) :=
  ParameterTensorRowPresentation.supported (inverseOpen f T).ι X

/-- The actual enlargement map preserves the independent forward and original backward legs. -/
def presentationEnlargement (X : Scheme.{u}ᵒᵖ) :
    fiberPresentation f T X ⟶ ambientPresentation T X :=
  SchemeModelRowSeed.inputMap (fiber f T)
    (supportedUnit (unionOpen f T).ι) (supportedUnit_naturality (unionOpen f T).ι)
    (ambient T) (supportedUnit T.ι) (supportedUnit_naturality T.ι)
    (enlargement f T) (supportedMap_unit (enlargementPair f T)) X

/-- The actual support restriction acts on the genuine inverse-image supported presentation. -/
def presentationRestriction (X : Scheme.{u}ᵒᵖ) :
    ambientPresentation T X ⟶ openPresentation f T X :=
  SchemeModelRowSeed.inputMap (ambient T) (supportedUnit T.ι) (supportedUnit_naturality T.ι)
    (openModel f T) (supportedUnit (inverseOpen f T).ι)
    (supportedUnit_naturality (inverseOpen f T).ι)
    (restriction f T) (supportedMap_unit (supportRestrictionPair f T)) X

/-- The original current-to-row comparison on union-supported objects. -/
def fiberPresentationComparison (X : Scheme.{u}ᵒᵖ) :=
  ParameterTensorRowPresentation.supportedComparison (unionOpen f T).ι X

/-- The original current-to-row comparison on the auxiliary support. -/
def ambientPresentationComparison (X : Scheme.{u}ᵒᵖ) :=
  ParameterTensorRowPresentation.supportedComparison T.ι X

/-- The original current-to-row comparison on the inverse-image support. -/
def openPresentationComparison (X : Scheme.{u}ᵒᵖ) :=
  ParameterTensorRowPresentation.supportedComparison (inverseOpen f T).ι X

/-- The actual enlargement and current comparisons form a strict whole-spectrum square. -/
theorem presentationEnlargement_square (X : Scheme.{u}ᵒᵖ) :
    (currentEnlargement f T).app X ≫ ambientPresentationComparison T X =
      fiberPresentationComparison f T X ≫ presentationEnlargement f T X :=
  SchemeModelRowSeed.comparison_inputMap (fiber f T)
    (supportedUnit (unionOpen f T).ι) (supportedUnit_naturality (unionOpen f T).ι)
    (ambient T) (supportedUnit T.ι) (supportedUnit_naturality T.ι)
    (enlargement f T) (supportedMap_unit (enlargementPair f T)) X

omit [IsOpenImmersion f] in
/-- The actual restriction and current comparisons retain the original open arrow. -/
theorem presentationRestriction_square (X : Scheme.{u}ᵒᵖ) :
    (currentRestriction f T).app X ≫ openPresentationComparison f T X =
      ambientPresentationComparison T X ≫ presentationRestriction f T X :=
  SchemeModelRowSeed.comparison_inputMap (ambient T)
    (supportedUnit T.ι) (supportedUnit_naturality T.ι)
    (openModel f T) (supportedUnit (inverseOpen f T).ι)
    (supportedUnit_naturality (inverseOpen f T).ι)
    (restriction f T) (supportedMap_unit (supportRestrictionPair f T)) X

end Quillen.PerfectComplexes.GlobalSectionChangeIndex.ParameterAuxiliarySupport
