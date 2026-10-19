/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.SchemeModelRowCellStrictification
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterTensorReturnedModel

/-! # Every ambient Bass stage from the genuine returned tensor action

The initial transformation is the actual returned tensor multiplication conjugated
by the specified evaluation/unit/unitor isomorphism. The unchanged Bass recursion
is applied before identifying its output with the original normalized forward.
Raw coefficient-square identification is a separate geometric consumer.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.KTheory.Bass
universe u
namespace Quillen.PerfectComplexes.ParameterTensorEvaluationRow
open GlobalSectionChangeIndex

/-- The whole independent cell at each actual Bass stage, starting from returned tensor data. -/
def strictifiedIteratedCell (Q : Scheme.{u}) (i : ℕ) (X : Scheme.{u}ᵒᵖ) :=
  SchemeModelRowStrictification.iteratedCell (ParameterModels.ambient Q)
    (ParameterLaurentUnit.ambientUnit Q) (ParameterLaurentUnit.ambientUnit_naturality Q)
    (returnedTensorModel Q) (returnedTensorIso Q) (returnedTensorUnit Q)
    (returnedTensorIso_unit Q) i X

/-- The complete cell equality is proved after the genuine tensor-started recursion. -/
theorem strictifiedIteratedCell_eq (Q : Scheme.{u}) (i : ℕ) (X : Scheme.{u}ᵒᵖ) :
    strictifiedIteratedCell Q i X =
      SchemeModelRowSeed.cell (ParameterModels.ambient Q)
        (ParameterLaurentUnit.ambientUnit Q) (ParameterLaurentUnit.ambientUnit_naturality Q) i X :=
  SchemeModelRowStrictification.iteratedCell_eq (ParameterModels.ambient Q)
    (ParameterLaurentUnit.ambientUnit Q) (ParameterLaurentUnit.ambientUnit_naturality Q)
    (returnedTensorModel Q) (returnedTensorIso Q) (returnedTensorUnit Q)
    (returnedTensorIso_unit Q) i X

/-- Normalize the actual tensor-started stage cell before its original cone boundary. -/
def strictifiedNormalizedForward (Q : Scheme.{u}) (i : ℕ) (X : Scheme.{u}ᵒᵖ) :=
  SchemeModelRowStrictification.normalizedForward (ParameterModels.ambient Q)
    (ParameterLaurentUnit.ambientUnit Q) (ParameterLaurentUnit.ambientUnit_naturality Q)
    (returnedTensorModel Q) (returnedTensorIso Q) (returnedTensorUnit Q)
    (returnedTensorIso_unit Q) i X

/-- Every original normalized forward equals the independently tensor-started forward. -/
theorem strictifiedNormalizedForward_eq (Q : Scheme.{u}) (i : ℕ) (X : Scheme.{u}ᵒᵖ) :
    strictifiedNormalizedForward Q i X =
      SchemeModelRowSeed.normalizedBoundary (ParameterModels.ambient Q)
        (ParameterLaurentUnit.ambientUnit Q) (ParameterLaurentUnit.ambientUnit_naturality Q) i X :=
  SchemeModelRowStrictification.normalizedForward_eq (ParameterModels.ambient Q)
    (ParameterLaurentUnit.ambientUnit Q) (ParameterLaurentUnit.ambientUnit_naturality Q)
    (returnedTensorModel Q) (returnedTensorIso Q) (returnedTensorUnit Q)
    (returnedTensorIso_unit Q) i X

end Quillen.PerfectComplexes.ParameterTensorEvaluationRow
