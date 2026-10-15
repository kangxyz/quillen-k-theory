/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientLaurentEvaluation
public import Quillen.AlgebraicGeometry.Scheme.CoefficientPolynomialLaurent
public import Quillen.Topology.Prespectrum.PushoutHomotopySquare
public import Quillen.Topology.Prespectrum.HomotopySquareInterchange
public import Quillen.Topology.Prespectrum.HomotopySquareBoundary

/-!
# Actual native coefficient source-leg evaluation

The raw target uses the original native polynomial and Laurent fibers, their actual scheme
pullbacks, the positive and inverse chart tracks in that order, and the original cone
contraction. Evaluation on the three span corners gives the actual span map and moves its
literal source leg through the unchanged polynomial evaluation track. Its interchange with
the original cone contraction keeps the evaluation and cone coordinates independent.

This source-leg comparison alone does not descend evaluation to the Bass cones: that descent
also needs the relative composition comparison of the two original chart tracks.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum Quillen.PolynomialBaseChange
open AlgebraicGeometry.Scheme.CoefficientBaseChange
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}}

/-- The original positive native chart retains the prescribed split geometric composition track. -/
def boundedFlatCoefficientLaurentPlusHomotopy (P : Over (Spec R)) (a : Under R) :
    Homotopy (boundedFlatPerfectPrespectrumMap (laurentProjection P a))
      (boundedFlatPerfectPrespectrumMap (polynomialProjection P a) ≫
        boundedFlatPerfectPrespectrumMap (laurentPlus P a)) :=
  (boundedFlatPerfectPrespectrumCompHomotopy (laurentPlus P a)
    (polynomialProjection P a)).cast
      (congrArg boundedFlatPerfectPrespectrumMap (laurentPlus_projection P a)) rfl

/-- The inverse native chart retains its own original split geometric composition track. -/
def boundedFlatCoefficientLaurentMinusHomotopy (P : Over (Spec R)) (a : Under R) :
    Homotopy (boundedFlatPerfectPrespectrumMap (laurentProjection P a))
      (boundedFlatPerfectPrespectrumMap (polynomialProjection P a) ≫
        boundedFlatPerfectPrespectrumMap (laurentMinus P a)) :=
  (boundedFlatPerfectPrespectrumCompHomotopy (laurentMinus P a)
    (polynomialProjection P a)).cast
      (congrArg boundedFlatPerfectPrespectrumMap (laurentMinus_projection P a)) rfl

/-- The raw native square uses the reversed positive track followed by the inverse track. -/
def boundedFlatCoefficientBassSquareHomotopy (P : Over (Spec R)) (a : Under R) :=
  (boundedFlatCoefficientLaurentPlusHomotopy P a).symm.trans
    (boundedFlatCoefficientLaurentMinusHomotopy P a)

/-- The actual raw comparison on the two original native polynomial-chart cylinders. -/
def boundedFlatCoefficientBassSquareComparison (P : Over (Spec R)) (a : Under R) :=
  HomotopyPushout.desc
    (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
    (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
    (boundedFlatPerfectPrespectrumMap (laurentPlus P a))
    (boundedFlatPerfectPrespectrumMap (laurentMinus P a))
    (boundedFlatCoefficientBassSquareHomotopy P a)

/-- The raw source leg uses the original positive polynomial projection and the left inclusion. -/
def boundedFlatCoefficientBassSourceLeg (P : Over (Spec R)) (a : Under R) :=
  boundedFlatPerfectPrespectrumMap (polynomialProjection P a) ≫
    HomotopyPushout.inl
      (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
      (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))

/-- The raw source leg recovers precisely the original positive-chart composite. -/
theorem boundedFlatCoefficientBassSourceLeg_comparison (P : Over (Spec R)) (a : Under R) :
    boundedFlatCoefficientBassSourceLeg P a ≫ boundedFlatCoefficientBassSquareComparison P a =
      boundedFlatPerfectPrespectrumMap (polynomialProjection P a) ≫
        boundedFlatPerfectPrespectrumMap (laurentPlus P a) := by
  unfold boundedFlatCoefficientBassSourceLeg boundedFlatCoefficientBassSquareComparison
  rw [Category.assoc, HomotopyPushout.inl_desc]

/-- The original native Laurent source map is null via its positive track and literal cone leg. -/
def boundedFlatCoefficientBassLaurentNullHomotopy (P : Over (Spec R)) (a : Under R) :
    Homotopy
      (boundedFlatPerfectPrespectrumMap (laurentProjection P a) ≫
        mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a))
      (zeroHom (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a))))
        (mappingCone (boundedFlatCoefficientBassSquareComparison P a))) := by
  have N := Homotopy.precomp (boundedFlatCoefficientBassSourceLeg P a)
    (mappingConeHomotopy (boundedFlatCoefficientBassSquareComparison P a))
  change Homotopy
    ((boundedFlatCoefficientBassSourceLeg P a ≫ boundedFlatCoefficientBassSquareComparison P a) ≫
      mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a)) (zeroHom _ _) at N
  rw [boundedFlatCoefficientBassSourceLeg_comparison] at N
  exact ((boundedFlatCoefficientLaurentPlusHomotopy P a).postcomp
    (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a))).trans N

variable {P Q : Over (Spec R)} (f : P ⟶ Q)

/-- The original three evaluations and polynomial tracks map the original fine span. -/
def boundedFlatCoefficientFullOpenBassSpanEvaluation (a : Under R) :
    StrictSquare.span (boundedFlatCoefficientFullOpenBassSquare f a) ⟶
      HomotopyPushout.prespectrum
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)) :=
  HomotopyPushout.mapOfHomotopies
    ((boundedFlatCoefficientFullOpenPrespectrumFunctor f).map
      ((polynomialUnderCoefficient R).app a))
    ((boundedFlatCoefficientFullOpenPrespectrumFunctor f).map
      ((polynomialUnderCoefficient R).app a))
    (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
    (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
    (boundedFlatCoefficientSectionEvaluationPrespectrumMap (op P, a))
    (boundedFlatCoefficientSectionEvaluationPrespectrumMap
      (op P, (polynomialUnderFunctor R).obj a))
    (boundedFlatCoefficientSectionEvaluationPrespectrumMap
      (op P, (polynomialUnderFunctor R).obj a))
    (boundedFlatCoefficientSectionEvaluationHomotopy
      (i := (op P, a)) (k := (op P, (polynomialUnderFunctor R).obj a))
      (𝟙 (op P), (polynomialUnderCoefficient R).app a))
    (boundedFlatCoefficientSectionEvaluationHomotopy
      (i := (op P, a)) (k := (op P, (polynomialUnderFunctor R).obj a))
      (𝟙 (op P), (polynomialUnderCoefficient R).app a))

/-- Span evaluation retains the original positive polynomial source endpoint literally. -/
theorem boundedFlatCoefficientFullOpenBassSourceLeg_evaluation (a : Under R) :
    StrictSquare.sourceLeg (boundedFlatCoefficientFullOpenBassSquare f a) ≫
      boundedFlatCoefficientFullOpenBassSpanEvaluation f a =
    ((boundedFlatCoefficientFullOpenPrespectrumFunctor f).map
        ((polynomialUnderCoefficient R).app a) ≫
      boundedFlatCoefficientSectionEvaluationPrespectrumMap
        (op P, (polynomialUnderFunctor R).obj a)) ≫
      HomotopyPushout.inl
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)) := by
  apply Hom.ext
  funext n
  ext x
  rfl

/-- The same polynomial evaluation track moves the unchanged native source leg. -/
def boundedFlatCoefficientFullOpenBassSourceLegEvaluationHomotopy (a : Under R) :
    Homotopy
      (StrictSquare.sourceLeg (boundedFlatCoefficientFullOpenBassSquare f a) ≫
        boundedFlatCoefficientFullOpenBassSpanEvaluation f a)
      (boundedFlatCoefficientSectionEvaluationPrespectrumMap (op P, a) ≫
        boundedFlatCoefficientBassSourceLeg P a) :=
  ((boundedFlatCoefficientSectionEvaluationHomotopy
    (i := (op P, a)) (k := (op P, (polynomialUnderFunctor R).obj a))
    (𝟙 (op P), (polynomialUnderCoefficient R).app a)).postcomp
      (HomotopyPushout.inl
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)))).cast
        (boundedFlatCoefficientFullOpenBassSourceLeg_evaluation f a).symm (Category.assoc _ _ _)

/-- Original source movement interchanges with the original raw cone contraction. -/
def boundedFlatCoefficientFullOpenBassSourceLegEvaluationConeSquare (a : Under R) :=
  Homotopy.Square.interchange
    (boundedFlatCoefficientFullOpenBassSourceLegEvaluationHomotopy f a)
    (mappingConeHomotopy (boundedFlatCoefficientBassSquareComparison P a))

/-- The evaluation time and cone time remain independent on every native source point. -/
theorem boundedFlatCoefficientFullOpenBassSourceLegEvaluationConeSquare_apply
    (a : Under R) (n : ℕ) (r s : unitInterval)
    (x : ((boundedFlatCoefficientFullOpenPrespectrumFunctor f).obj a).space n) :
    (boundedFlatCoefficientFullOpenBassSourceLegEvaluationConeSquare f a).level n (r, (s, x)) =
      (mappingConeHomotopy (boundedFlatCoefficientBassSquareComparison P a)).level n
        (s, (boundedFlatCoefficientFullOpenBassSourceLegEvaluationHomotopy f a).level n
          (r, x)) := rfl

/-- Interchange supplies the complete pasted source-leg/cone boundary. -/
def boundedFlatCoefficientFullOpenBassSourceLegEvaluationConeBoundary (a : Under R) :=
  (boundedFlatCoefficientFullOpenBassSourceLegEvaluationConeSquare f a).toBoundary

end Quillen.PerfectComplexes
