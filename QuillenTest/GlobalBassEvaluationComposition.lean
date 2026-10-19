/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationComposition

/-! Whole original global evaluation composition faces and independent structure time. -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.PerfectComplexes Quillen.PerfectComplexes.GlobalSectionChangeIndex
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open scoped Topology unitInterval
universe u
namespace QuillenTest.GlobalBassEvaluationComposition

/-- The first entire face is the original evaluation followed by split geometric composition. -/
theorem original_split_face {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (n : ℕ) (s : unitInterval) (x : (prespectrum (globalModel.obj (op Z))).space n) :
    (evaluationCompositionRelHomotopy f g).level n (0, (s, x)) =
      (evaluationCompositionSplitRoute f g).level n (s, x) :=
  ((evaluationCompositionRelHomotopy f g).level n).apply_zero (s, x)

/-- The second entire face keeps both original evaluation tracks. -/
theorem original_whiskered_face {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (n : ℕ) (s : unitInterval) (x : (prespectrum (globalModel.obj (op Z))).space n) :
    (evaluationCompositionRelHomotopy f g).level n (1, (s, x)) =
      (evaluationCompositionWhiskeredRoute f g).level n (s, x) :=
  ((evaluationCompositionRelHomotopy f g).level n).apply_one (s, x)

/-- Composition comparison, original track and spectrum structure coordinates stay independent. -/
theorem original_structure_time {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (n : ℕ) (a s t : unitInterval) (x : (prespectrum (globalModel.obj (op Z))).space n) :
    (evaluationCompositionRelHomotopy f g).level (n + 1)
        (a, (s, (prespectrum (globalModel.obj (op Z))).structureMap n x t)) =
      (prespectrum (modelOf (boundedFlatPerfectWaldhausen X))).structureMap n
        ((evaluationCompositionRelHomotopy f g).level n (a, (s, x))) t :=
  (evaluationCompositionRelHomotopy f g).comm n a s x t

/-- Both normalized raw composition routes use the same original chosen-zero target. -/
theorem raw_composite_selected_zero {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (evaluationRawMap g ≫ evaluationRawMap f).functor.obj
        (modelOf (boundedFlatPerfectWaldhausen Z)).waldhausen.zero =
      (evaluationRawMap (f ≫ g)).functor.obj
        (modelOf (boundedFlatPerfectWaldhausen Z)).waldhausen.zero := by
  rw [(evaluationRawMap g ≫ evaluationRawMap f).zero, (evaluationRawMap (f ≫ g)).zero]

end QuillenTest.GlobalBassEvaluationComposition
