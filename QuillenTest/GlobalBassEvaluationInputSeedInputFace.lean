/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputSeedInputFace

/-! Regression checks for the two original null sheets and whole input-first carrier face. -/
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum Quillen.PerfectComplexes
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace QuillenTest.GlobalBassEvaluationInputSeedInputFace
open GlobalBassEvaluation GlobalSectionChangeIndex CommonReferenceNerve
variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- Both independent sheets recover the original whole moving null at every native point. -/
theorem both_null_sheets (e : Bool) (n : ℕ) (r s : I)
    (x : (prespectrum (globalModel.obj (op Y))).space n) :
    InputSeedInputNull.nativeEval g n (InputSeedInputNull.parameter g e (r, s)) x =
      (InputPositive.nullSquare g).level n
        (r, (s, (sectionMap (projection.app Y)).map n x)) :=
  InputSeedInputNull.native g e n r s x

/-- The four whole null boundaries retain their selected source, target, rail and tip. -/
theorem null_boundaries (e : Bool) (t : I) :
    InputSeedInputNull.parameter g e (0, t) = InputSeedInputNull.sourcePath g e t ∧
    InputSeedInputNull.parameter g e (1, t) = InputSeedInputNull.targetPath g e t ∧
    InputSeedInputNull.parameter g e (t, 0) = InputSeedInputNull.edge g e 0 3 t ∧
    InputSeedInputNull.parameter g e (t, 1) = InputSeedInputNull.tip g e :=
  ⟨InputSeedInputNull.parameter_zero g e t, InputSeedInputNull.parameter_one g e t,
    InputSeedInputNull.parameter_left g e t, InputSeedInputNull.parameter_right g e t⟩

/-- The actual unit-first product retains the original order at independent scalar times. -/
theorem original_middle_product (n : ℕ) (r s : I)
    (x : (prespectrum (globalModel.obj (op Y))).space n) :
    prespectrumFamily (InputSeedCarrier.laurentRef g) (InputSeedInputUnitProduct.nodes g) n
      (InputSeedInputUnitProduct.scalar.{u+1} (r, s), x) =
      (evaluationComparison (laurent.map g)).level n
        (r, (GlobalSchemeLaurentTrack.homotopy (op Y)).level n (s, x)) :=
  InputSeedInputUnitProduct.native g n r s x

/-- Every product corner agrees as an entire dependent reference node before realization. -/
theorem product_corners (i : Fin 4) :
    InputSeedInputUnitProduct.nodes g i =
      InputSeedUnitNodes.nodes g (InputSeedInputUnitNodes.cornerIndex i) :=
  InputSeedInputUnitNodes.corners g i

/-- The initial whole unit rail is the original lower0 to shifted0 edge. -/
theorem source_unit_rail (s : I) :
    InputSeedInputUnitProduct.parameter g (0, s) =
      CommonReferenceNerve.parameter (InputSeedCarrier.laurentRef g)
        (InputSeedUnitNodes.nodes g) (Quillen.SimplexParameters.edge (k := 15) 0 8 s) :=
  InputSeedInputRails.source g s

/-- The terminal whole unit rail retains the complete lower3 to shifted3 references. -/
theorem target_unit_rail (s : I) :
    InputSeedInputUnitProduct.parameter g (1, s) =
      CommonReferenceNerve.parameter (InputSeedCarrier.laurentRef g)
        (InputSeedUnitNodes.nodes g) (Quillen.SimplexParameters.edge (k := 15) 3 11 s) :=
  InputSeedInputRails.target g s

/-- The ordinary product rail is the full original mixed chart comparison edge. -/
theorem ordinary_chart_rail (r : I) :
    InputSeedInputUnitProduct.parameter g (r, 0) =
      InputChartSquareParameter.edge g plus GlobalRawBass.plus_projection 0 3 r :=
  InputSeedInputRails.bottom_chart g r

/-- The upper product rail has the original actual common-unit reanchoring. -/
theorem shifted_chart_rail (r : I) :
    InputSeedInputUnitProduct.parameter g (r, 1) =
      mapParameter (CommonReferenceProduct.reanchor (InputSeedCarrier.commonUnit g))
        (InputChartSquareParameter.edge g plus GlobalRawBass.plus_projection 0 3 r) :=
  InputSeedInputRails.top_chart g r

/-- The full face retains the selected nested inverse-null/unit/null path word. -/
theorem selected_word (r s : I) :
    InputSeedInputFace.parameter g (r, s) = InputSeedInputFace.path g r s :=
  InputSeedInputFace.parameter_apply g r s

/-- The original full A and B words are retained before any native evaluation. -/
theorem source_target_words (s : I) :
    InputSeedInputFace.parameter g (0, s) = InputSeedInputFace.sourceWord g s ∧
    InputSeedInputFace.parameter g (1, s) = InputSeedInputFace.targetWord g s :=
  ⟨InputSeedInputFace.source g s, InputSeedInputFace.target g s⟩

/-- The two entire side edges remain fixed at their distinct original tips. -/
theorem fixed_distinct_tips (r : I) :
    InputSeedInputFace.parameter g (r, 0) = InputSeedInputNull.tip g false ∧
    InputSeedInputFace.parameter g (r, 1) = InputSeedInputNull.tip g true ∧
    InputSeedInputNull.tip g false ≠ InputSeedInputNull.tip g true :=
  ⟨InputSeedInputFace.zero g r, InputSeedInputFace.one g r, InputSeedCarrier.tips_distinct g⟩

/-- Every point is the original strict seed under the fixed whole positive cone homotopy. -/
theorem whole_positive_action (n : ℕ) (r s : I)
    (x : (prespectrum (globalModel.obj (op Y))).space n) :
    InputSeedInputNull.nativeEval g n (InputSeedInputFace.parameter g (r, s)) x =
      (InputPositive.coneHomotopy g).level n
        (r, Path.toContinuousMap ((InputPositive.strictSeed Y).map n x) s) :=
  InputSeedInputFace.positive_native g n r s x

/-- The entire first prescribed piece is recovered with all original free coordinates. -/
theorem original_first_piece (n : ℕ) (r s : I)
    (x : (prespectrum (globalModel.obj (op Y))).space n) :
    (GlobalRawBass.InputIdentityPositive.inclusion X).map n
      (InputSeedInputNull.nativeEval g n (InputSeedInputFace.parameter g (r, s)) x) =
      Path.toContinuousMap ((InputSeedWords.inputFirst g).level n (r, x)) s :=
  InputSeedInputFace.native g n r s x

/-- The full initial carrier word evaluates to the original first piece's entire initial edge. -/
theorem source_word_native (n : ℕ) (s : I)
    (x : (prespectrum (globalModel.obj (op Y))).space n) :
    (GlobalRawBass.InputIdentityPositive.inclusion X).map n
      (InputSeedInputNull.nativeEval g n (InputSeedInputFace.sourceWord g s) x) =
      Path.toContinuousMap ((InputSeedWords.inputFirst g).level n (0, x)) s := by
  rw [← InputSeedInputFace.source]
  exact InputSeedInputFace.native g n 0 s x

/-- The full terminal word retains its original nested target-null cone heights natively. -/
theorem target_word_native (n : ℕ) (s : I)
    (x : (prespectrum (globalModel.obj (op Y))).space n) :
    (GlobalRawBass.InputIdentityPositive.inclusion X).map n
      (InputSeedInputNull.nativeEval g n (InputSeedInputFace.targetWord g s) x) =
      Path.toContinuousMap ((InputSeedWords.inputFirst g).level n (1, x)) s := by
  rw [← InputSeedInputFace.target]
  exact InputSeedInputFace.native g n 1 s x

/-- The actual first face occupies exactly the original long word's first half. -/
theorem long_route_first_half (n : ℕ) (r s : I)
    (x : (prespectrum (globalModel.obj (op Y))).space n) :
    (GlobalRawBass.InputIdentityPositive.inclusion X).map n
      (InputSeedInputNull.nativeEval g n (InputSeedInputFace.parameter g (r, s)) x) =
      Path.toContinuousMap ((InputSeedWords.longRoute g).level n
        (Quillen.NativePathCells.lower r, x)) s :=
  (InputSeedInputFace.native g n r s x).trans
    ((InputSeedWords.inputFirst_apply g n r s x).trans
      (InputSeedWords.long_first g n r s x).symm)

end QuillenTest.GlobalBassEvaluationInputSeedInputFace
