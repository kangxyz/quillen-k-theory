/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalAuxiliaryCoefficientPairs
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalSupportedPairDiagram
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterAuxiliarySupportMaps
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportedOpenModels

/-!
# Actual auxiliary-supported integral coefficient Model comparisons

Each component first uses the complete parameter support-pair isomorphism and then the
original supported coefficient restriction. The three targets are the original G7 fine
fiber, auxiliary ambient, and supported full-open Models. Their original zero objects are
preserved by the actual Model arrows, without introducing a new coarse family.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.GlobalAuxiliaryParameterCoefficient
open GlobalSectionChangeIndex

variable (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))) (T : Q.left.Opens)

/-- The actual parameter auxiliary-supported Model maps to the original native fine Model. -/
def ambientComponent (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (ParameterAuxiliarySupport.ambient T).obj (specUnder.obj a) ⟶
      boundedFlatCoefficientSupportedAmbientModel T a :=
  pairSupported.map (parameterSupportPairIso Q T a).hom.op ≫
    supportedRestrictionModel _ (op Q, a) (boundedFlatCoefficientSupportOpen Q T a).ι

/-- The component retains the selected zero of the original native auxiliary Model. -/
theorem ambientComponent_zero (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (ambientComponent Q T a).functor.obj
        ((ParameterAuxiliarySupport.ambient T).obj (specUnder.obj a)).waldhausen.zero =
      (boundedFlatCoefficientSupportedAmbientModel T a).waldhausen.zero :=
  (ambientComponent Q T a).zero

variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))}
    (f : P ⟶ Q) [IsOpenImmersion f.left] (T : Q.left.Opens)

/-- The union support is exactly the old G7 native fiber Model. -/
theorem fiberModel_eq (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    boundedFlatCoefficientSupportedAmbientModel (T ⊔ f.left.opensRange) a =
      boundedFlatCoefficientSupportedFiberModel f T a := by
  exact congrArg (fun U : (space (op Q, a)).Opens =>
    boundedFlatCoefficientSupportedSectionModel (i := (op Q, a)) U.ι)
    (fiberSupportOpen_eq f T a).symm

omit [IsOpenImmersion f.left] in
/-- The inverse-image support is exactly the old G7 native full-open Model. -/
theorem openModel_eq (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    boundedFlatCoefficientSupportedAmbientModel (f.left ⁻¹ᵁ T) a =
      boundedFlatCoefficientSupportedFullOpenModel f T a := by
  exact congrArg (fun U : (space (op P, a)).Opens =>
    boundedFlatCoefficientSupportedSectionModel (i := (op P, a)) U.ι)
    (boundedFlatCoefficientOpenSupportOpen_eq f T a).symm

/-- The actual union-support comparison targets the original G7 fiber Model. -/
def fiberComponent (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (ParameterAuxiliarySupport.fiber f.left T).obj (specUnder.obj a) ⟶
      boundedFlatCoefficientSupportedFiberModel f T a :=
  ambientComponent Q (T ⊔ f.left.opensRange) a ≫ eqToHom (fiberModel_eq f T a)

/-- The actual inverse-image-support comparison targets the original G7 full-open Model. -/
def openComponent (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (ParameterAuxiliarySupport.openModel f.left T).obj (specUnder.obj a) ⟶
      boundedFlatCoefficientSupportedFullOpenModel f T a :=
  ambientComponent P (f.left ⁻¹ᵁ T) a ≫ eqToHom (openModel_eq f T a)

/-- The actual fiber comparison preserves the old G7 selected zero. -/
theorem fiberComponent_zero (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (fiberComponent f T a).functor.obj
        ((ParameterAuxiliarySupport.fiber f.left T).obj (specUnder.obj a)).waldhausen.zero =
      (boundedFlatCoefficientSupportedFiberModel f T a).waldhausen.zero :=
  (fiberComponent f T a).zero

omit [IsOpenImmersion f.left] in
/-- The actual full-open comparison preserves the old G7 selected zero. -/
theorem openComponent_zero (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (openComponent f T a).functor.obj
        ((ParameterAuxiliarySupport.openModel f.left T).obj (specUnder.obj a)).waldhausen.zero =
      (boundedFlatCoefficientSupportedFullOpenModel f T a).waldhausen.zero :=
  (openComponent f T a).zero

end Quillen.PerfectComplexes.GlobalAuxiliaryParameterCoefficient
