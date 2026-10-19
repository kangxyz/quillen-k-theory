/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterAuxiliaryCurrentLocalization
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterAuxiliaryRowPresentationNull

/-!
# Same-null localization for the independent null-conjugated row presentation

The actual current auxiliary lift transfers through the three genuine stable
presentation comparisons, retaining enlargement, restriction and every time
of the prescribed null. This bounded intermediate is not the final classical
cup-normalized presentation or an identification of all original negative
class maps and boundaries.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open Quillen.LoopPrespectrum
universe u
namespace Quillen.PerfectComplexes.ParameterAuxiliaryRowLocalization
open GlobalSectionChangeIndex ParameterAuxiliarySupport ParameterAuxiliaryCurrentFiber
variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f] (T : Q.Opens)

/-- The original auxiliary null defines the actual path-space lift on the row presentations. -/
def presentationLift (X : Scheme.{u}ᵒᵖ) :=
  homotopyFiberLift (presentationRestriction f T X) (presentationEnlargement f T X)
    (presentationNull f T X)

/-- The specified full null gives the strict square of the original path-space lifts. -/
theorem current_presentation_lift_square (X : Scheme.{u}ᵒᵖ) :
    currentLift f T X ≫ homotopyFiberMap
        (Arrow.homMk (f := Arrow.mk ((currentRestriction f T).app X))
          (g := Arrow.mk (presentationRestriction f T X))
          (ambientPresentationComparison T X) (openPresentationComparison f T X)
          (presentationRestriction_square f T X).symm) =
      fiberPresentationComparison f T X ≫ presentationLift f T X :=
  homotopyFiberLift_naturality
    ((currentEnlargement f T).app X) ((currentRestriction f T).app X)
    (presentationEnlargement f T X) (presentationRestriction f T X)
    ((currentNull f T).homotopy X) (presentationNull f T X)
    (fiberPresentationComparison f T X) (ambientPresentationComparison T X)
    (openPresentationComparison f T X)
    (presentationEnlargement_square f T X) (presentationRestriction_square f T X).symm
    (presentationNull_comparison f T X)

/-- All three genuine comparisons transport the entire same-null fiber lift. -/
theorem current_presentation_lift_stable_iff (X : Scheme.{u}ᵒᵖ) :
    IsStableEquivalence (currentLift f T X) ↔ IsStableEquivalence (presentationLift f T X) :=
  homotopyFiberLift_isStableEquivalence_iff
    ((currentEnlargement f T).app X) ((currentRestriction f T).app X)
    (presentationEnlargement f T X) (presentationRestriction f T X)
    ((currentNull f T).homotopy X) (presentationNull f T X)
    (fiberPresentationComparison f T X) (ambientPresentationComparison T X)
    (openPresentationComparison f T X)
    (presentationEnlargement_square f T X) (presentationRestriction_square f T X).symm
    (presentationNull_comparison f T X)
    (ParameterTensorRowPresentation.supportedComparison_stable (unionOpen f T).ι X)
    (ParameterTensorRowPresentation.supportedComparison_stable T.ι X)
    (ParameterTensorRowPresentation.supportedComparison_stable (inverseOpen f T).ι X)

/-- The actual integer-base auxiliary row lift is stable with the original G7 hypotheses. -/
theorem presentationLift_integer_isStableEquivalence
    [CompactSpace P] [CompactSpace Q] [QuasiSeparatedSpace Q] [CompactSpace T] :
    IsStableEquivalence (presentationLift f T (op integerBase)) :=
  (current_presentation_lift_stable_iff f T (op integerBase)).mp
    (currentLift_integer_isStableEquivalence f T)

/-- The same prescribed lift is stable at every original affine base parameter. -/
theorem presentationLift_spec_isStableEquivalence
    {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q)
    [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]
    [QuasiSeparatedSpace Q.left] (T : Q.left.Opens) [CompactSpace T]
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    IsStableEquivalence (presentationLift f.left T (specUnder.obj a)) :=
  (current_presentation_lift_stable_iff f.left T (specUnder.obj a)).mp
    (currentLift_spec_isStableEquivalence f T a)

/-- Every original signed stable degree sees the same actual presentation lift. -/
theorem presentationLift_integer_signed_isIso
    [CompactSpace P] [CompactSpace Q] [QuasiSeparatedSpace Q] [CompactSpace T] (d : ℤ) :
    IsIso ((stableHomotopyFunctor d).map (presentationLift f T (op integerBase))) :=
  presentationLift_integer_isStableEquivalence f T d

/-- Projection of the same lift is precisely the original presentation enlargement. -/
theorem presentationLift_projection (X : Scheme.{u}ᵒᵖ) :
    presentationLift f T X ≫ homotopyFiberProjection (presentationRestriction f T X) =
      presentationEnlargement f T X :=
  homotopyFiberLift_projection _ _ _

end Quillen.PerfectComplexes.ParameterAuxiliaryRowLocalization
