/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitSupportedReturnedCell
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterTensorSupportedInitialCell

/-! # The returned genuine tensor cell on the literal supported parameter Model -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u
namespace Quillen.PerfectComplexes.ParameterTensorSupportedRow
open GlobalSectionChangeIndex
variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]

/-- The actual internal supported coefficient Model map. -/
abbrev coefficientModel (X : Scheme.{u}ᵒᵖ) := supportedPairModelMap (coefficientPair f X)

/-- The returned genuine tensor cell uses the original projected Laurent unit. -/
def returnedTensorCell (X : Scheme.{u}ᵒᵖ) :=
  SupportedTensorEvaluation.returnedTensorCell (coefficientPair f X)
    (ParameterLaurentUnit.projectedLaurentScalar Q X)

/-- The original evaluation unit and tensor unitor remain the chosen moving endpoint. -/
def returnedMovement (X : Scheme.{u}ᵒᵖ) :=
  SupportedTensorEvaluation.returnedMovement (coefficientPair f X)

/-- The internal supported coefficient cell is the literal parameter initial cell at every level.
-/
theorem sectionCell_level (X : Scheme.{u}ᵒᵖ) (n : ℕ) :
    (SupportedTensorEvaluation.sectionCell (coefficientPair f X)
      (ParameterLaurentUnit.projectedLaurentScalar Q X)).level n =
      (initialCell f X).level n := rfl

/-- The actual supported moving-endpoint prism on the literal parameter Model. -/
def returnedPasting (X : Scheme.{u}ᵒᵖ) :
    ((initialCell f X).trans (returnedMovement f X)).RelHomotopy
      ((returnedMovement f X).trans (returnedTensorCell f X)) := by
  let J := SupportedTensorEvaluation.returnedPasting (coefficientPair f X)
    (ParameterLaurentUnit.projectedLaurentScalar Q X)
  refine J.ofLevels _ _ ?_ ?_
  · intro n
    apply Homotopy.trans_level_congr
    · exact (sectionCell_level f X n).symm
    · rfl
  · intro n
    rfl

end Quillen.PerfectComplexes.ParameterTensorSupportedRow
