/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalEvaluationUnitPasting
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalTensorUnitPrism

/-! Actual global evaluation faces and independent original track/structure coordinates. -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.PerfectComplexes Quillen.PerfectComplexes.GlobalSectionChangeIndex
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open scoped Topology unitInterval
universe u
namespace QuillenTest.GlobalEvaluationUnitPasting

/-- The original global track occupies the entire first comparison face. -/
theorem original_first_face {X Y : Scheme.{u}} (f : X ⟶ Y) (r : (Γ(X, ⊤))ˣ)
    (n : ℕ) (s : unitInterval) (x : (prespectrum (globalModel.obj (Opposite.op Y))).space n) :
    (evaluationUnitPasting f r).level n (0, (s, x)) =
      ((evaluationOldUnit f r).trans (evaluationComparison f)).level n (s, x) :=
  ((evaluationUnitPasting f r).level n).apply_zero (s, x)

/-- The original raw track occupies the entire other comparison face. -/
theorem original_last_face {X Y : Scheme.{u}} (f : X ⟶ Y) (r : (Γ(X, ⊤))ˣ)
    (n : ℕ) (s : unitInterval) (x : (prespectrum (globalModel.obj (Opposite.op Y))).space n) :
    (evaluationUnitPasting f r).level n (1, (s, x)) =
      ((evaluationComparison f).trans (evaluationNewUnit f r)).level n (s, x) :=
  ((evaluationUnitPasting f r).level n).apply_one (s, x)

/-- Comparison, original unit and spectrum structure parameters remain independent. -/
theorem original_structure_time {X Y : Scheme.{u}} (f : X ⟶ Y) (r : (Γ(X, ⊤))ˣ)
    (n : ℕ) (a s t : unitInterval)
    (x : (prespectrum (globalModel.obj (Opposite.op Y))).space n) :
    (evaluationUnitPasting f r).level (n + 1)
        (a, (s, (prespectrum (globalModel.obj (Opposite.op Y))).structureMap n x t)) =
      (prespectrum (modelOf (boundedFlatPerfectWaldhausen X))).structureMap n
        ((evaluationUnitPasting f r).level n (a, (s, x))) t :=
  (evaluationUnitPasting f r).comm n a s x t

/-- The genuine tensor prism retains its full original first face. -/
theorem tensor_first_face {X Y : Scheme.{u}} (f : X ⟶ Y) (r : (Γ(X, ⊤))ˣ) :
    (tensorEvaluationPasting f r).at 0 =
      (evaluatedTensorTrack f r).trans (tensorEvaluationTrack f) :=
  (tensorEvaluationPasting f r).at_zero

/-- The actual normalized evaluation still sends the original selected zero literally to zero. -/
theorem evaluation_selected_zero (X : Scheme.{u}ᵒᵖ) :
    (evaluationModel X).functor.obj (globalModel.obj X).waldhausen.zero =
      (modelOf (boundedFlatPerfectWaldhausen X.unop)).waldhausen.zero :=
  (evaluationModel X).zero

end QuillenTest.GlobalEvaluationUnitPasting
