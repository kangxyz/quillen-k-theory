/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Quillen.Topology.Prespectrum.ConeSquareMapMovingCoherence
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSpanComposition
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassConeFaces

/-!
# Coefficient Bass Conditional Laws

Native conditional assembly of whole ORIGINAL coefficient Bass laws.
The comparison squares in the input types are live geometric obligations, not constructed here.

The identity API accepts any whole original-span identity homotopy with its comparison square;
prescribed polynomial faces are not required.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Quillen.LoopPrespectrum
open Quillen.PolynomialBaseChange AlgebraicGeometry.Scheme.CoefficientBaseChange
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- Paste exactly the two original Bass comparison homotopies before taking any cone. -/
def boundedFlatCoefficientBassCompositeComparison :=
  coneSquarePastedHomotopy
    (boundedFlatCoefficientBassSquareComparison P a)
    (boundedFlatCoefficientBassSquareComparison P b)
    (boundedFlatCoefficientBassSquareComparison P c)
    (boundedFlatCoefficientPolynomialSpanMap P u)
    (boundedFlatPerfectPrespectrumMap (coefficientMap P ((laurentUnderFunctor R).map u)))
    (boundedFlatCoefficientPolynomialSpanMap P v)
    (boundedFlatPerfectPrespectrumMap (coefficientMap P ((laurentUnderFunctor R).map v)))
    (boundedFlatCoefficientBassComparisonHomotopy P u)
    (boundedFlatCoefficientBassComparisonHomotopy P v)

/-- The exact missing geometric comparison of the original Bass square homotopies.
On a polynomial cylinder this square has a THIRD independent geometric parameter. -/
abbrev BoundedFlatCoefficientBassComparisonCompositionSquare :=
  (boundedFlatCoefficientBassComparisonHomotopy P (u ≫ v)).Square
    (boundedFlatCoefficientBassCompositeComparison P u v)
    (Homotopy.precomp (boundedFlatCoefficientBassSquareComparison P a)
      (boundedFlatCoefficientLaurentCompositionHomotopy P u v))
    ((boundedFlatCoefficientPolynomialSpanCompositionHomotopy P u v).postcomp
      (boundedFlatCoefficientBassSquareComparison P c))

/-- A producer of the actual geometric comparison square completes the whole ORIGINAL cone law.
The whole Laurent face and every original cone-cylinder point are retained. -/
def boundedFlatCoefficientBassConeCompositionOfComparisonSquare
    (Q : BoundedFlatCoefficientBassComparisonCompositionSquare P u v) :
    Homotopy (boundedFlatCoefficientBassConeMap P (u ≫ v))
      (boundedFlatCoefficientBassConeMap P u ≫ boundedFlatCoefficientBassConeMap P v) :=
  coneSquareCompositionHomotopyOfSquare
    (boundedFlatCoefficientBassSquareComparison P a)
    (boundedFlatCoefficientBassSquareComparison P b)
    (boundedFlatCoefficientBassSquareComparison P c)
    (boundedFlatCoefficientPolynomialSpanMap P u)
    (boundedFlatPerfectPrespectrumMap (coefficientMap P ((laurentUnderFunctor R).map u)))
    (boundedFlatCoefficientPolynomialSpanMap P v)
    (boundedFlatPerfectPrespectrumMap (coefficientMap P ((laurentUnderFunctor R).map v)))
    (boundedFlatCoefficientBassComparisonHomotopy P u)
    (boundedFlatCoefficientBassComparisonHomotopy P v)
    (boundedFlatCoefficientBassComparisonHomotopy P (u ≫ v))
    (boundedFlatCoefficientPolynomialSpanCompositionHomotopy P u v)
    (boundedFlatCoefficientLaurentCompositionHomotopy P u v) Q

/-- The conditional whole law has exactly the prescribed original Laurent composition face. -/
theorem boundedFlatCoefficientBassConeCompositionOfComparisonSquare_inclusion
    (Q : BoundedFlatCoefficientBassComparisonCompositionSquare P u v)
    (n : ℕ) (r : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (laurentUnderFunctor R).obj a)))).space n) :
    (boundedFlatCoefficientBassConeCompositionOfComparisonSquare P u v Q).level n
      (r, (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a)).map n x) =
        (boundedFlatCoefficientBassConeCompositionInclusionHomotopy P u v).level n (r, x) := rfl

/-- The conditional entire composition law loops with the original independent path coordinate. -/
def boundedFlatCoefficientBassStepCompositionOfComparisonSquare
    (Q : BoundedFlatCoefficientBassComparisonCompositionSquare P u v) :
    Homotopy (boundedFlatCoefficientBassStepMap P (u ≫ v))
      (boundedFlatCoefficientBassStepMap P u ≫ boundedFlatCoefficientBassStepMap P v) :=
  (boundedFlatCoefficientBassConeCompositionOfComparisonSquare P u v Q).parameterLooping.cast
    rfl (parameterLoopingFunctor.map_comp _ _)

/-- The identity of the polynomial coefficient map includes its original normalization track. -/
def boundedFlatCoefficientPolynomialIdentityHomotopy (a : Under R) :
    Homotopy
      (boundedFlatPerfectPrespectrumMap
        (coefficientMap P ((polynomialUnderFunctor R).map (𝟙 a))))
      (𝟙 (originalPrespectrum (boundedFlatPerfectWaldhausen
        (space (op P, (polynomialUnderFunctor R).obj a))))) :=
  (boundedFlatCoefficientIdentityHomotopy P ((polynomialUnderFunctor R).obj a)).cast
    (congrArg (fun k ↦ boundedFlatPerfectPrespectrumMap (coefficientMap P k))
      ((polynomialUnderFunctor R).map_id a)).symm rfl

/-- The first live identity obligation retains both original geometric unit tracks.
Its construction needs the unit faces of chosen-zero normalization as well as pullback units. -/
abbrev BoundedFlatCoefficientPolynomialIdentitySquare (a : Under R) :=
  (boundedFlatCoefficientPolynomialSquareHomotopy P (𝟙 a)).Square
    (coneSquareIdentityTrack (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)))
    (Homotopy.precomp (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
      (boundedFlatCoefficientPolynomialIdentityHomotopy P a))
    ((boundedFlatCoefficientIdentityHomotopy P a).postcomp
      (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)))

/-- The next identity obligation compares the original whole Bass homotopy to its identity square.
The input `A` must still be produced for the original span, with its prescribed polynomial faces. -/
abbrev BoundedFlatCoefficientBassComparisonIdentitySquare (a : Under R)
    (A : Homotopy (boundedFlatCoefficientPolynomialSpanMap P (𝟙 a))
      (𝟙 (HomotopyPushout.prespectrum
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))))) :=
  (boundedFlatCoefficientBassComparisonHomotopy P (𝟙 a)).Square
    (coneSquareIdentityTrack (boundedFlatCoefficientBassSquareComparison P a))
    (Homotopy.precomp (boundedFlatCoefficientBassSquareComparison P a)
      (boundedFlatCoefficientLaurentIdentityHomotopy P a))
    (A.postcomp (boundedFlatCoefficientBassSquareComparison P a))

/-- Complete original unit comparison data yields the whole original cone identity. -/
def boundedFlatCoefficientBassConeIdentityOfComparisonSquare (a : Under R)
    (A : Homotopy (boundedFlatCoefficientPolynomialSpanMap P (𝟙 a))
      (𝟙 (HomotopyPushout.prespectrum
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)))))
    (Q : BoundedFlatCoefficientBassComparisonIdentitySquare P a A) :
    Homotopy (boundedFlatCoefficientBassConeMap P (𝟙 a))
      (𝟙 (mappingCone (boundedFlatCoefficientBassSquareComparison P a))) :=
  coneSquareIdentityHomotopyOfSquare (boundedFlatCoefficientBassSquareComparison P a)
    (boundedFlatCoefficientBassComparisonHomotopy P (𝟙 a)) A
    (boundedFlatCoefficientLaurentIdentityHomotopy P a) Q

/-- The conditional whole unit law preserves the original Laurent identity track exactly. -/
theorem boundedFlatCoefficientBassConeIdentityOfComparisonSquare_inclusion (a : Under R)
    (A : Homotopy (boundedFlatCoefficientPolynomialSpanMap P (𝟙 a))
      (𝟙 (HomotopyPushout.prespectrum
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)))))
    (Q : BoundedFlatCoefficientBassComparisonIdentitySquare P a A)
    (n : ℕ) (r : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (laurentUnderFunctor R).obj a)))).space n) :
    (boundedFlatCoefficientBassConeIdentityOfComparisonSquare P a A Q).level n
      (r, (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a)).map n x) =
        (boundedFlatCoefficientBassConeIdentityInclusionHomotopy P a).level n (r, x) := rfl

/-- Parameter looping preserves the complete conditional original unit law. -/
def boundedFlatCoefficientBassStepIdentityOfComparisonSquare (a : Under R)
    (A : Homotopy (boundedFlatCoefficientPolynomialSpanMap P (𝟙 a))
      (𝟙 (HomotopyPushout.prespectrum
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)))))
    (Q : BoundedFlatCoefficientBassComparisonIdentitySquare P a A) :
    Homotopy (boundedFlatCoefficientBassStepMap P (𝟙 a))
      (𝟙 (parameterLooping (mappingCone (boundedFlatCoefficientBassSquareComparison P a)))) :=
  (boundedFlatCoefficientBassConeIdentityOfComparisonSquare P a A Q).parameterLooping.cast
    rfl (parameterLoopingFunctor.map_id _)

end Quillen.PerfectComplexes
