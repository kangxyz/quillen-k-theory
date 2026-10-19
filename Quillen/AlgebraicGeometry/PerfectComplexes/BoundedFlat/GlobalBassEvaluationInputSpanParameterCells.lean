/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputSpanParameterWord
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputSpanParameterNorm
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputSpan
public import Quillen.Topology.Prespectrum.NativeMovingSquareCells
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNervePointwiseFamily

/-!
# The original native cells of the mixed-reference moving span

The finite attached projection and normalization prisms recover each whole native cell,
including all shared half and quarter boundaries. Evaluation is only pointwise on the nerve;
its restrictions to the compact parameters are the existing continuous finite families.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.GlobalBassEvaluation.InputSpanParameterCells
open GlobalSectionChangeIndex InputSpanParameterWord Quillen.NativePathCells
variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The existing pointwise evaluator, restricted below to actual compact scalar families. -/
def ev (n : ℕ) (x : (prespectrum (globalModel.obj (op Y))).space n)
    (z : Carrier g) :=
  CommonReferenceNerve.pointwisePrespectrumFamily (InputMixedDesc.sourceMap g) n z x

/-- The exact original native moving square before the selected boundary correction. -/
def movingNative := HomotopyPushout.identicalLegMovingSquare
  (sectionMap (projection.app Y)) (boundedFlatPerfectPrespectrumMap (projection.app X))
  (InputSpan.sourceLeg g) (InputSpan.pastedLeg g) (evaluationComparison g)
  (evaluationComparison (polynomial.map g)) (InputSpan.legSquare g)

/-- Every point of each attached projection square retains the original native square. -/
theorem chart_native (k : laurent ⟶ polynomial)
    (hk : ∀ Z, k.app Z ≫ projection.app Z = GlobalRawBass.laurentProjection.app Z)
    (n : ℕ) (x : (prespectrum (globalModel.obj (op Y))).space n) (q s : unitInterval) :
    ev g n x (chartSwap g k hk (s, q)) =
      (boundedFlatPerfectPrespectrumMap (k.app X)).map n
        ((InputSpan.legSquare g).level n (q, (s, x))) := by
  exact (CommonReferenceNerve.pointwisePrespectrumFamily_eq_compact
    (InputMixedDesc.sourceMap g) (InputSpanParameterNodes.parameter g k hk) n (q, s) x).trans
      (DFunLike.congr_fun (InputSpanParameterNodes.native g k hk n) ((q, s), x))

/-- The whole split normalization prism acts at the original moving evaluation input. -/
theorem normalization_native (k : laurent ⟶ polynomial)
    (hk : ∀ Z, k.app Z ≫ projection.app Z = GlobalRawBass.laurentProjection.app Z)
    (n : ℕ) (x : (prespectrum (globalModel.obj (op Y))).space n) (q s : unitInterval) :
    ev g n x (normalizationSwap g k hk (s, q)) =
      (boundedFlatPerfectPrespectrumCompHomotopy (k.app X) (projection.app X)).level n
        (s, (evaluationComparison g).level n (q, x)) := by
  exact (CommonReferenceNerve.pointwisePrespectrumFamily_eq_compact
    (InputMixedDesc.sourceMap g) (InputSpanParameterPrism.parameter g k hk) n (q, s) x).trans
      (InputSpanParameterPrism.native g k hk n q s x)

/-- Both whole overlap halves retain the original signs and exact original time coordinate. -/
theorem overlap_native (n : ℕ) (x : (prespectrum (globalModel.obj (op Y))).space n)
    (q s : unitInterval) :
    ev g n x (overlapSwap g (s, q)) = (GlobalRawBass.squareHomotopy X).level n
      (s, (evaluationComparison g).level n (q, x)) := by
  rcases cover s with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · unfold overlapSwap GlobalRawBass.squareHomotopy
    rw [Quillen.ScalarRectangle.homotopy_lower, Homotopy.trans_lower_cell]
    exact normalization_native g plus GlobalRawBass.plus_projection n x q (unitInterval.symm t)
  · unfold overlapSwap GlobalRawBass.squareHomotopy
    rw [Quillen.ScalarRectangle.homotopy_upper, Homotopy.trans_upper_cell]
    exact normalization_native g minus GlobalRawBass.minus_projection n x q t

/-- All three complete cells recover the actual native moving span after raw comparison. -/
theorem moving_native (n : ℕ) (x : (prespectrum (globalModel.obj (op Y))).space n)
    (q s : unitInterval) :
    ev g n x (movingParameter g (q, s)) =
      (GlobalRawBass.comparison X).map n ((movingNative g).level n (q, (s, x))) := by
  rcases three_cover s with ⟨t, rfl⟩ | ⟨t, rfl⟩ | ⟨t, rfl⟩
  · change ev g n x ((chartSwap g plus GlobalRawBass.plus_projection).trans _ (lower t, q)) = _
    rw [Quillen.ScalarRectangle.homotopy_lower]
    unfold movingNative
    rw [HomotopyPushout.identicalMoving_lower]
    exact chart_native g plus GlobalRawBass.plus_projection n x q t
  · change ev g n x ((chartSwap g plus GlobalRawBass.plus_projection).trans _
      (upper (lower t), q)) = _
    rw [Quillen.ScalarRectangle.homotopy_upper, Quillen.ScalarRectangle.homotopy_lower]
    unfold movingNative
    rw [HomotopyPushout.identicalMoving_middle, GlobalRawBass.comparison_cylinder]
    exact overlap_native g n x q t
  · change ev g n x ((chartSwap g plus GlobalRawBass.plus_projection).trans _
      (upper (upper t), q)) = _
    rw [Quillen.ScalarRectangle.homotopy_upper, Quillen.ScalarRectangle.homotopy_upper]
    unfold movingNative
    rw [HomotopyPushout.identicalMoving_upper]
    exact chart_native g minus GlobalRawBass.minus_projection n x q (unitInterval.symm t)

end Quillen.PerfectComplexes.GlobalBassEvaluation.InputSpanParameterCells
