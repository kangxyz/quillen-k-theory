/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.SchemeModelRowCellStrictification
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitSupportedReturnedModel
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterTensorSupportedRow

/-! # Every supported Bass stage from the genuine returned tensor action

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
open Quillen.KTheory.Bass Quillen.FunctorIdentityAutomorphism
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.ParameterTensorSupportedRow
open GlobalSectionChangeIndex GeometricSeedCospan
variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]

/-- The actual returned tensor map with its literal parameter Model endpoints. -/
def strictificationModel (X : Scheme.{u}ᵒᵖ) :
    (ParameterModels.supported f).obj X ⟶
      (ParameterModels.supported f).obj (laurent.op.obj X) :=
  SupportedTensorEvaluation.returnedTensorModel (coefficientPair f X)

/-- The specified return isomorphism with its actual parameter coefficient source. -/
def strictificationIso (X : Scheme.{u}ᵒᵖ) :
    ((ParameterModels.supported f).map (coefficient.app X)).functor ≅
      (strictificationModel f X).functor :=
  SupportedTensorEvaluation.returnedTensorIso (coefficientPair f X)

/-- The unchanged returned tensor multiplication at the original Laurent scalar. -/
def strictificationUnit (X : Scheme.{u}ᵒᵖ) :
    (strictificationModel f X).functor ⟶ (strictificationModel f X).functor :=
  SupportedTensorEvaluation.returnedTensorUnit (coefficientPair f X)
    (ParameterLaurentUnit.projectedLaurentScalar Q X)

/-- The original supported intertwining holds with the literal parameter endpoints. -/
theorem strictificationIso_unit (X : Scheme.{u}ᵒᵖ) :
    (onFunctor ((ParameterModels.supported f).map (coefficient.app X)).functor
      (ParameterLaurentTrack.supportedUnit f X)).hom ≫ (strictificationIso f X).hom =
    (strictificationIso f X).hom ≫ strictificationUnit f X := by
  ext K
  exact NatTrans.congr_app
    (SupportedTensorEvaluation.returnedTensorIso_unit (coefficientPair f X)
      (ParameterLaurentUnit.projectedLaurentScalar Q X)) K

/-- The whole independent cell at each actual Bass stage, starting from returned tensor data. -/
def strictifiedIteratedCell (i : ℕ) (X : Scheme.{u}ᵒᵖ) :=
  SchemeModelRowStrictification.iteratedCell (ParameterModels.supported f)
    (ParameterLaurentTrack.supportedUnit f) (ParameterLaurentTrack.supportedUnit_naturality f)
    (strictificationModel f) (strictificationIso f) (strictificationUnit f)
    (strictificationIso_unit f) i X

/-- The complete cell equality is proved after the genuine tensor-started recursion. -/
theorem strictifiedIteratedCell_eq (i : ℕ) (X : Scheme.{u}ᵒᵖ) :
    strictifiedIteratedCell f i X =
      SchemeModelRowSeed.cell (ParameterModels.supported f)
        (ParameterLaurentTrack.supportedUnit f) (ParameterLaurentTrack.supportedUnit_naturality f)
        i X :=
  SchemeModelRowStrictification.iteratedCell_eq (ParameterModels.supported f)
    (ParameterLaurentTrack.supportedUnit f) (ParameterLaurentTrack.supportedUnit_naturality f)
    (strictificationModel f) (strictificationIso f) (strictificationUnit f)
    (strictificationIso_unit f) i X

/-- Normalize the actual tensor-started stage cell before its original cone boundary. -/
def strictifiedNormalizedForward (i : ℕ) (X : Scheme.{u}ᵒᵖ) :=
  SchemeModelRowStrictification.normalizedForward (ParameterModels.supported f)
    (ParameterLaurentTrack.supportedUnit f) (ParameterLaurentTrack.supportedUnit_naturality f)
    (strictificationModel f) (strictificationIso f) (strictificationUnit f)
    (strictificationIso_unit f) i X

/-- Every original normalized forward equals the independently tensor-started forward. -/
theorem strictifiedNormalizedForward_eq (i : ℕ) (X : Scheme.{u}ᵒᵖ) :
    strictifiedNormalizedForward f i X =
      SchemeModelRowSeed.normalizedBoundary (ParameterModels.supported f)
        (ParameterLaurentTrack.supportedUnit f) (ParameterLaurentTrack.supportedUnit_naturality f)
        i X :=
  SchemeModelRowStrictification.normalizedForward_eq (ParameterModels.supported f)
    (ParameterLaurentTrack.supportedUnit f) (ParameterLaurentTrack.supportedUnit_naturality f)
    (strictificationModel f) (strictificationIso f) (strictificationUnit f)
    (strictificationIso_unit f) i X

end Quillen.PerfectComplexes.ParameterTensorSupportedRow
