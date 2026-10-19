/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputSeedNaturality

/-! Regression checks for the complete original mixed seed routes and their relative comparison. -/
noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum Quillen.PerfectComplexes
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Topology unitInterval
universe u
namespace QuillenTest.GlobalBassEvaluationInputSeedNaturality
open GlobalBassEvaluation GlobalSectionChangeIndex CommonReferenceNerve
open Quillen.NativePathCells
variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The complete strict-input face retains every comparison and seed time. -/
theorem strict_face (n : ℕ) (r s : I)
    (x : (prespectrum (globalModel.obj (op Y))).space n) :
    (GlobalRawBass.InputIdentityPositive.inclusion X).map n
      (CutOpenCarrier.nativeEval (InputSeedCarrier.polyRef g) (InputSeedCarrier.chart (X := X))
        (InputSeedCarrier.laurentRef g) (InputSeedCarrier.ordinary g) (InputSeedCarrier.shifted g)
        n (InputSeedStrictFace.parameter g (r, s)) x) =
      Path.toContinuousMap ((InputSeedWords.seedFirst g).level n (r, x)) s :=
  InputSeedStrictFace.native g n r s x

/-- The complete raw-post face uses the independently defined original raw input. -/
theorem post_face (n : ℕ) (r s : I)
    (x : (prespectrum (globalModel.obj (op Y))).space n) :
    (GlobalRawBass.InputIdentityPositive.inclusion X).map n
      (CutOpenCarrier.nativeEval (InputSeedCarrier.polyRef g) (InputSeedCarrier.chart (X := X))
        (InputSeedCarrier.laurentRef g) (InputSeedCarrier.ordinary g) (InputSeedCarrier.shifted g)
        n (InputSeedPostFace.parameter g (r, s)) x) =
      Path.toContinuousMap ((InputSeedWords.seedSecond g).level n (r, x)) s :=
  InputSeedPostFace.native g n r s x

/-- The complete moving-evaluation face recovers the original raw seed at every input. -/
theorem evaluation_face (n : ℕ) (r s : I)
    (x : (prespectrum (globalModel.obj (op Y))).space n) :
    (GlobalRawBass.InputIdentityPositive.inclusion X).map n
      (CutOpenCarrier.nativeEval (InputSeedCarrier.polyRef g) (InputSeedCarrier.chart (X := X))
        (InputSeedCarrier.laurentRef g) (InputSeedCarrier.ordinary g) (InputSeedCarrier.shifted g)
        n (InputSeedEvalFace.parameter g (r, s)) x) =
      Path.toContinuousMap ((InputSeedWords.evaluationSecond g).level n (r, x)) s :=
  InputSeedEvalFace.native g n r s x

/-- The original two-half binary path retains its independently moving evaluation input. -/
theorem binary_native (n : ℕ) (r s : I)
    (x : (prespectrum (globalModel.obj (op Y))).space n) :
    compactPrespectrumFamily (InputSeedCarrier.laurentRef g) (InputSeedEvalBinary.parameter g)
      n ((r, s), x) =
      (GlobalRawBass.plusHomotopy X).level n (s, (evaluationComparison g).level n (r, x)) :=
  InputSeedEvalBinary.native g n r s x

/-- The selected binary surface is the entire terminal normalization-prism face. -/
theorem binary_surface (r s : I) : InputSeedEvalBinary.parameter g (r, s) =
    InputChartReference.prismParameter g plus GlobalRawBass.plus_projection (r, (1, s)) :=
  InputSeedEvalBinary.parameter_terminal g r s

/-- Both distinct sheets recover the unchanged binary/cylinder source-null word. -/
theorem moving_null (e : Bool) (n : ℕ) (r s : I)
    (x : (prespectrum (globalModel.obj (op Y))).space n) :
    InputSeedInputNull.nativeEval g n (InputSeedEvalNull.parameter g e (r, s)) x =
      (GlobalRawBass.InputIdentityPositive.sourceNull X).level n
        (s, (evaluationComparison g).level n (r, x)) :=
  InputSeedEvalNull.native g e n r s x

/-- The whole common A word agrees before native evaluation at every seed time. -/
theorem a_word (s : I) : InputSeedStrictFace.parameter g (0, s) =
    InputSeedInputFace.parameter g (0, s) := InputSeedSourceSeam.face g s

/-- The whole common B word agrees before native evaluation at every seed time. -/
theorem b_word (s : I) : InputSeedPostFace.parameter g (0, s) =
    InputSeedInputFace.parameter g (1, s) := InputSeedPostSourceSeam.face g s

/-- The whole common C word agrees before native evaluation at every seed time. -/
theorem c_word (s : I) : InputSeedPostFace.parameter g (1, s) =
    InputSeedTransitionFace.parameter g (0, s) := InputSeedPostTargetSeam.face g s

/-- The whole common D word agrees before native evaluation at every seed time. -/
theorem d_word (s : I) : InputSeedStrictFace.parameter g (1, s) =
    InputSeedEvalFace.parameter g (0, s) := InputSeedStrictTargetSeam.face g s

/-- The whole common E word agrees before native evaluation at every seed time. -/
theorem e_word (s : I) : InputSeedTransitionFace.parameter g (1, s) =
    InputSeedEvalFace.parameter g (1, s) := InputSeedRawTargetSeam.face g s

/-- The entire prescribed long route retains its original concatenation clocks. -/
theorem long_route (n : ℕ) (r s : I)
    (x : (prespectrum (globalModel.obj (op Y))).space n) :
    (GlobalRawBass.InputIdentityPositive.inclusion X).map n
      (CutOpenCarrier.nativeEval (InputSeedCarrier.polyRef g) (InputSeedCarrier.chart (X := X))
        (InputSeedCarrier.laurentRef g) (InputSeedCarrier.ordinary g) (InputSeedCarrier.shifted g)
        n (InputSeedRoutes.longParameter g (r, s)) x) =
      Path.toContinuousMap ((InputSeedWords.longRoute g).level n (r, x)) s :=
  InputSeedRoutes.long_native g n r s x

/-- The actual assembled carrier retains the original middle and final quarter clocks. -/
theorem original_quarters (n : ℕ) (r s : I)
    (x : (prespectrum (globalModel.obj (op Y))).space n) :
    (GlobalRawBass.InputIdentityPositive.inclusion X).map n
      (CutOpenCarrier.nativeEval (InputSeedCarrier.polyRef g) (InputSeedCarrier.chart (X := X))
        (InputSeedCarrier.laurentRef g) (InputSeedCarrier.ordinary g) (InputSeedCarrier.shifted g)
        n (InputSeedRoutes.longParameter g (upper (lower r), s)) x) =
      (GlobalRawBass.coneMap g).map n ((conjugation Y).level n (r, (s, x))) ∧
    (GlobalRawBass.InputIdentityPositive.inclusion X).map n
      (CutOpenCarrier.nativeEval (InputSeedCarrier.polyRef g) (InputSeedCarrier.chart (X := X))
        (InputSeedCarrier.laurentRef g) (InputSeedCarrier.ordinary g) (InputSeedCarrier.shifted g)
        n (InputSeedRoutes.longParameter g (upper (upper r), s)) x) =
      (GlobalRawBass.InputSeed.conjugateComparison g).level n
        (r, (s, (GlobalBassEvaluation.evaluation Y).map n x)) :=
  ⟨(InputSeedRoutes.long_native g n (upper (lower r)) s x).trans
      (InputSeedWords.long_second g n r s x),
    (InputSeedRoutes.long_native g n (upper (upper r)) s x).trans
      (InputSeedWords.long_third g n r s x)⟩

/-- The entire prescribed short route retains its original concatenation clocks. -/
theorem short_route (n : ℕ) (r s : I)
    (x : (prespectrum (globalModel.obj (op Y))).space n) :
    (GlobalRawBass.InputIdentityPositive.inclusion X).map n
      (CutOpenCarrier.nativeEval (InputSeedCarrier.polyRef g) (InputSeedCarrier.chart (X := X))
        (InputSeedCarrier.laurentRef g) (InputSeedCarrier.ordinary g) (InputSeedCarrier.shifted g)
        n (InputSeedRoutes.shortParameter g (r, s)) x) =
      Path.toContinuousMap ((InputSeedWords.shortRoute g).level n (r, x)) s :=
  InputSeedRoutes.short_native g n r s x

/-- The two complete original native routes admit the actual relative comparison. -/
def originalComparison :
    (InputSeedWords.longRoute g).RelHomotopy (InputSeedWords.shortRoute g) :=
  InputSeedNaturality.comparison g

/-- Both selected whole faces survive the relative comparison literally. -/
theorem original_faces (n : ℕ) (s : I)
    (x : (prespectrum (globalModel.obj (op Y))).space n) :
    (originalComparison g).level n (0, (s, x)) =
      (InputSeedWords.longRoute g).level n (s, x) ∧
    (originalComparison g).level n (1, (s, x)) =
      (InputSeedWords.shortRoute g).level n (s, x) :=
  ⟨((originalComparison g).level n).apply_zero (s, x),
    ((originalComparison g).level n).apply_one (s, x)⟩

/-- Every comparison slice fixes both original seed-input endpoint maps. -/
theorem fixed_endpoint_maps (n : ℕ) (r : I)
    (x : (prespectrum (globalModel.obj (op Y))).space n) :
    (originalComparison g).level n (r, (0, x)) =
      (strictSeed Y ≫ (InputSeedWords.strictInput g ≫ stepEvaluation X)).map n x ∧
    (originalComparison g).level n (r, (1, x)) =
      (GlobalBassEvaluation.evaluation Y ≫
        (boundedFlatPerfectPrespectrumMap g ≫ GlobalRawBass.transition X)).map n x :=
  ⟨((originalComparison g).at r).at_zero n x, ((originalComparison g).at r).at_one n x⟩

/-- The full based line is fixed independently of comparison and route time. -/
theorem based_line (n : ℕ) (r s : I) :
    (originalComparison g).level n
      (r, (s, (prespectrum (globalModel.obj (op Y))).point n)) =
      (GlobalRawBass.step X).point n :=
  ((originalComparison g).at r).at_point n s

/-- All independent comparison, route and loop times recover the actual finite extension. -/
theorem extension_value (n : ℕ) (r s t : I)
    (x : (prespectrum (globalModel.obj (op Y))).space n) :
    Path.toContinuousMap ((originalComparison g).level n (r, (s, x))) t =
      (GlobalRawBass.InputIdentityPositive.inclusion X).map n
        (CutOpenCarrier.nativeEval (InputSeedCarrier.polyRef g) (InputSeedCarrier.chart (X := X))
          (InputSeedCarrier.laurentRef g) (InputSeedCarrier.ordinary g) (InputSeedCarrier.shifted g)
          n ((InputSeedRoutes.surfaces g).boundary.carrier ((r, s), t)) x) :=
  InputSeedNaturality.comparison_apply g n r s t x

/-- The original structure coordinate stays independent of all three other times. -/
theorem independent_structure (n : ℕ) (r s t v : I)
    (x : (prespectrum (globalModel.obj (op Y))).space n) :
    Path.toContinuousMap ((originalComparison g).level (n + 1)
      (r, (s, (prespectrum (globalModel.obj (op Y))).structureMap n x t))) v =
    Path.toContinuousMap ((GlobalRawBass.step X).structureMap n
      ((originalComparison g).level n (r, (s, x))) t) v :=
  congrArg (fun p ↦ Path.toContinuousMap p v) ((originalComparison g).comm n r s x t)

/-- The two carrier tips remain distinct, including after assembling both entire routes. -/
theorem distinct_tips :
    CutOpenCarrier.tipMinus (InputSeedCarrier.polyRef g) (InputSeedCarrier.chart (X := X))
      (InputSeedCarrier.laurentRef g) (InputSeedCarrier.ordinary g) (InputSeedCarrier.shifted g) ≠
    CutOpenCarrier.tipPlus (InputSeedCarrier.polyRef g) (InputSeedCarrier.chart (X := X))
      (InputSeedCarrier.laurentRef g) (InputSeedCarrier.ordinary g) (InputSeedCarrier.shifted g) :=
  InputSeedCarrier.tips_distinct g

/-- Neither moving evaluation time identifies the ordinary and shifted whole seed edges. -/
theorem moving_tips_distinct (r s : I) :
    InputSeedEvalFace.parameter g (r, 0) ≠ InputSeedEvalFace.parameter g (s, 1) := by
  rw [InputSeedEvalFace.zero, InputSeedEvalFace.one]
  exact InputSeedCarrier.tips_distinct g

end QuillenTest.GlobalBassEvaluationInputSeedNaturality
