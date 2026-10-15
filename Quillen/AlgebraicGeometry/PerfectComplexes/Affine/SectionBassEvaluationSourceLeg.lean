/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Polynomial.Laurent.BaseChange
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionBassEvaluation
public import Quillen.Topology.Prespectrum.HomotopySquareInterchange
public import Quillen.Topology.Prespectrum.HomotopySquareBoundary

/-!
# Original source-leg movement under section evaluation

The unchanged polynomial evaluation track moves the actual strict Bass source leg into its raw
geometric counterpart. Interchange with the original cone contraction retains both parameters.
-/
@[expose] public section

open CommRingCat.PolynomialLaurent

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent
universe u
namespace Quillen.PerfectComplexes
variable (R : CommRingCat.{u})

/-- Actual span evaluation retains the literal positive polynomial source endpoint. -/
theorem boundedFlatAffineSectionBassSourceLeg_evaluation :
    StrictSquare.sourceLeg (boundedFlatAffineSectionBassSquare R) ≫
      boundedFlatAffineSectionBassSpanEvaluation R =
    (boundedFlatAffineSectionPrespectrumFunctor.map (coefficient R) ≫
      boundedFlatAffineSectionEvaluationPrespectrumMap (.of (Polynomial R))) ≫
        HomotopyPushout.inl (boundedFlatPerfectPrespectrumMap (polynomialProjection R))
          (boundedFlatPerfectPrespectrumMap (polynomialProjection R)) := by
  apply Hom.ext
  funext n
  ext x
  rfl

/-- The original coefficient homotopy moves the actual source leg through the raw span. -/
def boundedFlatAffineSectionBassSourceLegEvaluationHomotopy :
    Homotopy
      (StrictSquare.sourceLeg (boundedFlatAffineSectionBassSquare R) ≫
        boundedFlatAffineSectionBassSpanEvaluation R)
      (boundedFlatAffineSectionEvaluationPrespectrumMap R ≫ boundedFlatBassSourceLeg R) :=
  ((boundedFlatAffineSectionEvaluationCoefficientHomotopy (coefficient R)).postcomp
    (HomotopyPushout.inl (boundedFlatPerfectPrespectrumMap (polynomialProjection R))
      (boundedFlatPerfectPrespectrumMap (polynomialProjection R)))).cast
        (boundedFlatAffineSectionBassSourceLeg_evaluation R).symm (Category.assoc _ _ _)

/-- The original source-leg movement through the unchanged raw cone nullhomotopy. -/
def boundedFlatAffineSectionBassSourceLegEvaluationConeSquare :=
  Homotopy.Square.interchange (boundedFlatAffineSectionBassSourceLegEvaluationHomotopy R)
    (mappingConeHomotopy (boundedFlatBassSquareComparison R))

/-- Both original polynomial and cone parameters remain independent. -/
theorem boundedFlatAffineSectionBassSourceLegEvaluationConeSquare_apply (n : ℕ)
    (r s : unitInterval) (x : (boundedFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    (boundedFlatAffineSectionBassSourceLegEvaluationConeSquare R).level n (r, (s, x)) =
      (mappingConeHomotopy (boundedFlatBassSquareComparison R)).level n
        (s, (boundedFlatAffineSectionBassSourceLegEvaluationHomotopy R).level n (r, x)) := rfl

/-- The actual interchange square supplies its whole pasted boundary. -/
def boundedFlatAffineSectionBassSourceLegEvaluationConeBoundary :=
  (boundedFlatAffineSectionBassSourceLegEvaluationConeSquare R).toBoundary

end Quillen.PerfectComplexes
