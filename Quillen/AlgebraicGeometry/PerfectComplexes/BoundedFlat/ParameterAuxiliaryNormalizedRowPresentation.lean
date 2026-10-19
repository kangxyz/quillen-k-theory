/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterTensorNormalizedRowPresentation
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterAuxiliaryTelescopeNull
public import Quillen.KTheory.Bass.SchemeModelRowNormalizedInput

/-! # The actual auxiliary-support diagram of normalized tensor-row presentations

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
def normalizedFiberPresentation (X : Scheme.{u}ᵒᵖ) :=
  ParameterTensorNormalizedRowPresentation.supported (unionOpen f T).ι X

/-- The original auxiliary support gives the middle presentation. -/
def normalizedAmbientPresentation (X : Scheme.{u}ᵒᵖ) :=
  ParameterTensorNormalizedRowPresentation.supported T.ι X

/-- The inverse-image support gives the actual open presentation. -/
def normalizedOpenPresentation (X : Scheme.{u}ᵒᵖ) :=
  ParameterTensorNormalizedRowPresentation.supported (inverseOpen f T).ι X

/-- The actual enlargement map preserves the normalized forward and original backward legs. -/
def normalizedPresentationEnlargement (X : Scheme.{u}ᵒᵖ) :
    normalizedFiberPresentation f T X ⟶ normalizedAmbientPresentation T X :=
  SchemeModelRowSeed.normalizedInputMap (fiber f T)
    (supportedUnit (unionOpen f T).ι) (supportedUnit_naturality (unionOpen f T).ι)
    (ambient T) (supportedUnit T.ι) (supportedUnit_naturality T.ι)
    (enlargement f T) (supportedMap_unit (enlargementPair f T)) X

/-- The actual support restriction acts on the genuine inverse-image supported presentation. -/
def normalizedPresentationRestriction (X : Scheme.{u}ᵒᵖ) :
    normalizedAmbientPresentation T X ⟶ normalizedOpenPresentation f T X :=
  SchemeModelRowSeed.normalizedInputMap (ambient T) (supportedUnit T.ι)
    (supportedUnit_naturality T.ι)
    (openModel f T) (supportedUnit (inverseOpen f T).ι)
    (supportedUnit_naturality (inverseOpen f T).ι)
    (restriction f T) (supportedMap_unit (supportRestrictionPair f T)) X

/-- The original current-to-row comparison on union-supported objects. -/
def normalizedFiberPresentationComparison (X : Scheme.{u}ᵒᵖ) :=
  ParameterTensorNormalizedRowPresentation.supportedComparison (unionOpen f T).ι X

/-- The original current-to-row comparison on the auxiliary support. -/
def normalizedAmbientPresentationComparison (X : Scheme.{u}ᵒᵖ) :=
  ParameterTensorNormalizedRowPresentation.supportedComparison T.ι X

/-- The original current-to-row comparison on the inverse-image support. -/
def normalizedOpenPresentationComparison (X : Scheme.{u}ᵒᵖ) :=
  ParameterTensorNormalizedRowPresentation.supportedComparison (inverseOpen f T).ι X

/-- The actual enlargement and current comparisons form a strict whole-spectrum square. -/
theorem normalizedPresentationEnlargement_square (X : Scheme.{u}ᵒᵖ) :
    (currentEnlargement f T).app X ≫ normalizedAmbientPresentationComparison T X =
      normalizedFiberPresentationComparison f T X ≫ normalizedPresentationEnlargement f T X :=
  SchemeModelRowSeed.normalizedComparison_inputMap (fiber f T)
    (supportedUnit (unionOpen f T).ι) (supportedUnit_naturality (unionOpen f T).ι)
    (ambient T) (supportedUnit T.ι) (supportedUnit_naturality T.ι)
    (enlargement f T) (supportedMap_unit (enlargementPair f T)) X

omit [IsOpenImmersion f] in
/-- The actual restriction and current comparisons retain the original open arrow. -/
theorem normalizedPresentationRestriction_square (X : Scheme.{u}ᵒᵖ) :
    (currentRestriction f T).app X ≫ normalizedOpenPresentationComparison f T X =
      normalizedAmbientPresentationComparison T X ≫ normalizedPresentationRestriction f T X :=
  SchemeModelRowSeed.normalizedComparison_inputMap (ambient T)
    (supportedUnit T.ι) (supportedUnit_naturality T.ι)
    (openModel f T) (supportedUnit (inverseOpen f T).ι)
    (supportedUnit_naturality (inverseOpen f T).ι)
    (restriction f T) (supportedMap_unit (supportRestrictionPair f T)) X

end Quillen.PerfectComplexes.GlobalSectionChangeIndex.ParameterAuxiliarySupport
