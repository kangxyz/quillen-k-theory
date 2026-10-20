/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassConnectiveTelescopeComparison
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientFullOpenBassLocalization
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportedFullOpenBassLocalization
public import Quillen.KTheory.Bass.StrictDiagramSelfMap

/-!
# The fine Bass nonconnective K model

These names expose the existing native section Bass telescope, its original Laurent seed,
and its actual stable Bass self-map. They introduce no new spectrum construction and assert
no comparison or uniqueness with an independently specified classical model.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.KTheory.Bass
open Quillen.Waldhausen.IteratedS CommRingCat.PolynomialLaurent
universe u
namespace Quillen.PerfectComplexes.FineBassK
variable {R : CommRingCat.{u}}

/-- The existing fine Bass completion as its original coefficient diagram. -/
abbrev spectrumDiagram (Q : Over (Spec R)) :=
  boundedFlatCoefficientAmbientBassTelescopeFunctor Q

/-- The fine nonconnective K prespectrum at an actual coefficient. -/
abbrev spectrum (Q : Over (Spec R)) (a : Under R) := (spectrumDiagram Q).obj a

/-- The existing completion with support on the complement of the specified open. -/
abbrev supportedDiagram {P Q : Over (Spec R)} (f : P ⟶ Q) [IsOpenImmersion f.left] :=
  boundedFlatCoefficientSupportedBassTelescopeFunctor f

/-- The supported fine nonconnective K prespectrum at an actual coefficient. -/
abbrev supportedSpectrum {P Q : Over (Spec R)} (f : P ⟶ Q) [IsOpenImmersion f.left]
    (a : Under R) := (supportedDiagram f).obj a

/-- The specified original seed induces the actual map to the Bass image of this telescope. -/
abbrev bassMap (Q : Over (Spec R)) :=
  strictDiagramTelescopeSelfMap (laurentUnderSquareFunctor R)
    (boundedFlatCoefficientAmbientBassSeed Q)

/-- The fine model is Bass stable as a prespectrum, not merely by abstract group identifications. -/
theorem bassMap_isStableEquivalence (Q : Over (Spec R)) (a : Under R) :
    IsStableEquivalence ((bassMap Q).app a) := by
  let : ∀ (i : ℕ) (a : Under R) (n : ℕ), T1Space
      ((((strictDiagramIterate (laurentUnderSquareFunctor R) i).obj
        (boundedFlatCoefficientAmbientPrespectrumFunctor Q)).obj a).space n) :=
    fun i a n => modelDiagramIterateSpaceT1Space (laurentUnderSquareFunctor R) i
      (boundedFlatCoefficientSectionModelRow Q) a n
  exact strictDiagramTelescopeSelfMap_isStableEquivalence (laurentUnderSquareFunctor R)
    (F := boundedFlatCoefficientAmbientPrespectrumFunctor Q)
    (boundedFlatCoefficientAmbientBassSeed Q) a

/-- The supported original seed gives the actual supported Bass self-map. -/
abbrev supportedBassMap {P Q : Over (Spec R)} (f : P ⟶ Q) [IsOpenImmersion f.left] :=
  strictDiagramTelescopeSelfMap (laurentUnderSquareFunctor R)
    (boundedFlatCoefficientSupportedBassSeed f)

/-- Supported Bass stability uses the actual finite Model topology, with no compactness premise. -/
theorem supportedBassMap_isStableEquivalence {P Q : Over (Spec R)} (f : P ⟶ Q)
    [IsOpenImmersion f.left] (a : Under R) :
    IsStableEquivalence ((supportedBassMap f).app a) := by
  let : ∀ (i : ℕ) (a : Under R) (n : ℕ), T1Space
      ((((strictDiagramIterate (laurentUnderSquareFunctor R) i).obj
        (boundedFlatCoefficientSupportedPrespectrumFunctor f)).obj a).space n) :=
    fun i a n => modelDiagramIterateSpaceT1Space (laurentUnderSquareFunctor R) i
      (boundedFlatCoefficientSupportedModelFunctor f) a n
  exact strictDiagramTelescopeSelfMap_isStableEquivalence (laurentUnderSquareFunctor R)
    (F := boundedFlatCoefficientSupportedPrespectrumFunctor f)
    (boundedFlatCoefficientSupportedBassSeed f) a

/-- The original connective perfect K groups, including K₀, identify with this same completion. -/
abbrev connectiveComparison (Q : Over (Spec R)) [CompactSpace Q.left]
    [QuasiSeparatedSpace Q.left] (n : ℕ) :=
  boundedFlatCoefficientAmbientKTelescopeComparison Q n

/-- The original Bass negative groups identify with this same completion, retaining the quotient. -/
abbrev negativeComparison (Q : Over (Spec R)) [CompactSpace Q.left]
    [QuasiSeparatedSpace Q.left] (i : ℕ) :=
  boundedFlatCoefficientAmbientNegativeKTelescopeComparison Q i

section Localization
variable {P Q : Over (Spec R)} (f : P ⟶ Q) [IsOpenImmersion f.left]

/-- The actual support-forgetting arrow of the selected fine model. -/
abbrev supportForget := boundedFlatCoefficientSupportedBassTelescopeForget f

/-- The actual full-open restriction, whose target is the same ambient model on the open. -/
abbrev restriction := boundedFlatCoefficientAmbientBassTelescopeFullOpen f

/-- The original localization null, not a newly chosen null. -/
abbrev localizationNull := boundedFlatCoefficientSupportedBassTelescopeFullOpenNull f

/-- The auxiliary-supported model, with acyclicity on the specified open T. -/
abbrev auxiliarySpectrum (T : Q.left.Opens) (a : Under R) :=
  (boundedFlatCoefficientSupportedAmbientBassTelescopeFunctor T).obj a

/-- The intersection-support model, with acyclicity on the union of T and the removed open. -/
abbrev intersectionSpectrum (T : Q.left.Opens) (a : Under R) :=
  (boundedFlatCoefficientSupportedFiberBassTelescopeFunctor f T).obj a

/-- The original support-enlargement arrow for the auxiliary localization sequence. -/
abbrev auxiliaryForget (T : Q.left.Opens) :=
  boundedFlatCoefficientSupportedFiberBassTelescopeForget f T

/-- The original auxiliary-supported full-open restriction. -/
abbrev auxiliaryRestriction (T : Q.left.Opens) :=
  boundedFlatCoefficientSupportedAmbientBassTelescopeFullOpen f T

/-- The original whole auxiliary localization null. -/
abbrev auxiliaryNull (T : Q.left.Opens) :=
  boundedFlatCoefficientSupportedFiberBassTelescopeFullOpenNull f T

variable [CompactSpace P.left] [CompactSpace Q.left] [QuasiSeparatedSpace Q.left]

/-- The basic fiber lift is defined by the existing arrows and original whole null. -/
abbrev localizationFiberMap (a : Under R) :=
  boundedFlatCoefficientSupportedBassTelescopeFullOpenFiberMap f a

/-- TT localization for the selected fine Bass model: its specified fiber lift is stable
in every signed degree. This does not assert a levelwise homotopy equivalence. -/
theorem localization (a : Under R) :
    IsStableEquivalence (localizationFiberMap f a) :=
  boundedFlatCoefficientSupportedBassTelescopeFullOpenFiberMap_isStableEquivalence f a

/-- The auxiliary lift is the existing lift from the original enlarged support and null. -/
abbrev auxiliaryFiberMap (T : Q.left.Opens) (a : Under R) :=
  boundedFlatCoefficientSupportedFiberBassTelescopeFullOpenFiberMap f T a

/-- Auxiliary-supported TT localization for the same selected fine model and compact T. -/
theorem auxiliaryLocalization (T : Q.left.Opens) [CompactSpace T] (a : Under R) :
    IsStableEquivalence (auxiliaryFiberMap f T a) :=
  boundedFlatCoefficientSupportedFiberBassTelescopeFullOpenFiberMap_isStableEquivalence f T a

end Localization
end Quillen.PerfectComplexes.FineBassK
