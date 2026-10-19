/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalEvaluationNaturality
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalEvaluationInputSquare
public import Quillen.Waldhausen.SmallModel.CoefficientCoherence
public import Quillen.Aglib.CategoryTheory.Functor.IsoRouteConjugation

/-!
# The original global evaluation comparison as a normalized coefficient square

The comparison retains its original raw pullback normalization and the independently chosen
source and target evaluation normalizations. This exact isomorphism identity is the first
input to the arbitrary-scheme Bass evaluation composition comparison.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open Quillen.Waldhausen Quillen.CategoryTheory.GrothendieckSections
universe u
namespace Quillen.PerfectComplexes.GlobalSectionChangeIndex

attribute [local irreducible] evaluationNormalizationIso originalCoefficientIso

/-- The original geometric Model edge retains its exact small coefficient comparison. -/
theorem evaluationComparisonIso_smallCoefficient {X Y : Scheme.{u}} (f : X ⟶ Y) :
    evaluationComparisonIso f =
      isoSquareConjugate
        (smallCoefficientIso boundedFlatPerfectPseudofunctor f.op (evaluationRawNormalization f))
        (evaluationNormalizationIso (op Y)) (evaluationNormalizationIso (op X)) := by
  simp only [evaluationComparisonIso, evaluationMiddleIso, isoSquareConjugate,
    smallCoefficientIso, normalizedCoefficientIso, smallModelWhiskerIso,
    evaluationPullbackIso_original, Iso.symm_symm_eq, isoWhiskerRight_trans,
    Iso.trans_assoc]
  rfl

end Quillen.PerfectComplexes.GlobalSectionChangeIndex
