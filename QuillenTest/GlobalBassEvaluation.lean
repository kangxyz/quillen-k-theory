/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationSeed
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationEquivalence

/-! Original global Bass chart, null, seed and independent-coordinate regression checks. -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.PerfectComplexes Quillen.PerfectComplexes.GlobalBassEvaluation
open Quillen.PerfectComplexes.GlobalSectionChangeIndex
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Topology unitInterval
universe u
namespace QuillenTest.GlobalBassEvaluation

/-- The moving comparison keeps the original positive geometric evaluation on the whole face. -/
theorem positive_face (X : Scheme.{u}) (n : ℕ) (r : unitInterval)
    (x : (GlobalSchemeLaurentTrack.diagram.obj (op (polynomial.obj X))).space n) :
    (comparisonHomotopy X).level n
      (r, (HomotopyPushout.inl (sectionMap (projection.app X))
        (sectionMap (projection.app X))).map n x) =
      (evaluationComparison (plus.app X)).level n (r, x) :=
  comparisonHomotopy_inl X n r x

/-- The other face keeps the distinct original inverse-coordinate evaluation track. -/
theorem negative_face (X : Scheme.{u}) (n : ℕ) (r : unitInterval)
    (x : (GlobalSchemeLaurentTrack.diagram.obj (op (polynomial.obj X))).space n) :
    (comparisonHomotopy X).level n
      (r, (HomotopyPushout.inr (sectionMap (projection.app X))
        (sectionMap (projection.app X))).map n x) =
      (evaluationComparison (minus.app X)).level n (r, x) :=
  comparisonHomotopy_inr X n r x

/-- The complete original null reaches the raw source-null through original Laurent movement. -/
theorem null_last_face (X : Scheme.{u}) (n : ℕ) (s : unitInterval)
    (x : (GlobalSchemeLaurentTrack.diagram.obj (op X)).space n) :
    (GlobalBassEvaluationNull.originalNullComparison X).level n (1, (s, x)) =
      ((GlobalBassEvaluationNull.laurentMovement X).trans
        (GlobalBassEvaluationNull.originalNewNull X)).level n (s, x) :=
  ((GlobalBassEvaluationNull.originalNullComparison X).level n).apply_one (s, x)

/-- The compared seed retains independent comparison and output-loop coordinates. -/
theorem seed_loop_time (X : Scheme.{u}) (n : ℕ) (r s : unitInterval)
    (x : (GlobalSchemeLaurentTrack.diagram.obj (op X)).space n) :
    Path.toContinuousMap ((seedHomotopy X).level n (r, x)) s =
      (conjugation X).level n (r, (s, x)) := seedHomotopy_apply X n r s x

/-- Comparison, loop and spectrum structure coordinates are simultaneously independent. -/
theorem seed_structure_time (X : Scheme.{u}) (n : ℕ) (r s t : unitInterval)
    (x : (GlobalSchemeLaurentTrack.diagram.obj (op X)).space n) :
    Path.toContinuousMap ((seedHomotopy X).level (n + 1)
      (r, (GlobalSchemeLaurentTrack.diagram.obj (op X)).structureMap n x t)) s =
    Path.toContinuousMap ((GlobalRawBass.step X).structureMap n
      ((seedHomotopy X).level n (r, x)) t) s :=
  congrArg (fun p => Path.toContinuousMap p s) ((seedHomotopy X).comm n r x t)

/-- The actual one-step map is stable and compares the two original seeds at once. -/
theorem stable_original_seed (X : Scheme.{u}) :
    IsStableEquivalence (stepEvaluation X) ∧
      Nonempty (Homotopy (strictSeed X ≫ stepEvaluation X)
        (evaluation X ≫ GlobalRawBass.transition X)) :=
  ⟨stepEvaluation_isStableEquivalence X, ⟨seedHomotopy X⟩⟩

end QuillenTest.GlobalBassEvaluation
