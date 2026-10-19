/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterAuxiliaryRowNullEndpoint

/-! # The original auxiliary row null retains all based faces at every finite Bass stage -/
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite Quillen.LoopPrespectrum Quillen.KTheory.Bass
open Quillen.PerfectComplexes.GlobalSectionChangeIndex.ParameterAuxiliarySupport
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Quillen.KTheory.Bass.GeometricSeedCospan
open scoped Topology unitInterval
universe u
namespace QuillenTest.ParameterAuxiliaryRowNull
variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f] (T : Q.Opens)

/-- Null time and the positive row coordinate independently fix the original point. -/
theorem positive_based_face (i : ℕ) (X : Scheme.{u}ᵒᵖ) (k : ℕ) (t s : unitInterval) :
    Path.toContinuousMap ((fullRowNull f T i X).level (k + 1)
      (t, Path.refl ((ModelDiagramRowRefinement.source squareFunctor i (fiber f T) X).point
        (k + 2)))) s =
      (ModelDiagramRowRefinement.source squareFunctor i (openModel f T) X).point (k + 2) := by
  rw [fullRowNull_succ]
  exact (fullConeNull f T i X).at_point (k + 2) t

/-- The explicit degree-zero double row retains the same point for three independent times. -/
theorem zero_based_face (i : ℕ) (X : Scheme.{u}ᵒᵖ) (t s a : unitInterval) :
    Path.toContinuousMap (Path.toContinuousMap ((fullRowNull f T i X).level 0
      (t, Path.refl (Path.refl
        ((ModelDiagramRowRefinement.source squareFunctor i (fiber f T) X).point 2)))) s) a =
      (ModelDiagramRowRefinement.source squareFunctor i (openModel f T) X).point 2 := by
  rw [fullRowNull_zero]
  exact (fullConeNull f T i X).at_point 2 t

/-- Literal-zero endpoint casts preserve the entire original time and row values. -/
theorem prescribed_time (i : ℕ) (X : Scheme.{u}ᵒᵖ) (n : ℕ) :
    (fullRowNullToZero f T i X).level n = (fullRowNull f T i X).level n :=
  fullRowNullToZero_level f T i X n

end QuillenTest.ParameterAuxiliaryRowNull
