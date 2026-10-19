/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputRawPastedParameter
public import
Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputRawChartProductWhole
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveCubeExtension
public import Quillen.Topology.Prespectrum.NativeH1CellOps

/-!
# The whole raw input homotopy on the evaluated strict cylinder

The three attached compact surfaces recover the actual raw input homotopy after the original
span evaluation. All three height cells, their shared boundaries, and the independent raw
homotopy time are retained as an equality of continuous maps at every prespectrum level.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.GlobalBassEvaluation.InputRawPastedNative
open GlobalSectionChangeIndex Quillen.NativePathCells InputRawPastedParameter
variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The original evaluation acts on the strict cylinder without changing either parameter. -/
def inputParameter (n : ℕ) :
    C((unitInterval × unitInterval) × (prespectrum (globalModel.obj (op Y))).space n,
      unitInterval × (GlobalRawBass.span Y).space n) :=
  ⟨fun z => (z.1.1, (spanEvaluation Y).map n
    (HomotopyPushout.cylinder (sectionMap (projection.app Y))
      (sectionMap (projection.app Y)) n (z.1.2, z.2))), by fun_prop⟩

/-- This family uses the actual raw input homotopy, rather than a replacement square. -/
def nativeFamily (n : ℕ) :=
  ((GlobalRawBass.inputComparisonHomotopy g).level n).comp (inputParameter (Y := Y) n)

/-- The first original cylinder cell is the actual positive raw square at moving evaluation. -/
theorem native_lower (n : ℕ) (r s : unitInterval)
    (x : (prespectrum (globalModel.obj (op Y))).space n) :
    nativeFamily g n ((r, lower s), x) =
      (GlobalRawBass.plusSquareHomotopy g).level n
        (r, (evaluationComparison (projection.app Y)).level n (s, x)) :=
  (congrArg (fun y => (GlobalRawBass.inputComparisonHomotopy g).level n (r, y))
    (HomotopyPushout.mapOfHomotopies_lower_cell
      (sectionMap (projection.app Y)) (sectionMap (projection.app Y))
      (boundedFlatPerfectPrespectrumMap (projection.app Y))
      (boundedFlatPerfectPrespectrumMap (projection.app Y))
      (evaluation Y) (evaluation (polynomial.obj Y)) (evaluation (polynomial.obj Y))
      (evaluationComparison (projection.app Y)) (evaluationComparison (projection.app Y))
      n s x)).trans (GlobalRawBass.inputComparisonHomotopy_inl g n r _)

/-- The middle original cylinder cell keeps the whole selected raw descent surface. -/
theorem native_middle (n : ℕ) (r s : unitInterval)
    (x : (prespectrum (globalModel.obj (op Y))).space n) :
    nativeFamily g n ((r, upper (lower s)), x) =
      (GlobalRawBass.inputDescPasting g).toSquare.level n
        (r, (s, (evaluation Y).map n x)) :=
  (congrArg (fun y => (GlobalRawBass.inputComparisonHomotopy g).level n (r, y))
    (HomotopyPushout.mapOfHomotopies_middle_cell
      (sectionMap (projection.app Y)) (sectionMap (projection.app Y))
      (boundedFlatPerfectPrespectrumMap (projection.app Y))
      (boundedFlatPerfectPrespectrumMap (projection.app Y))
      (evaluation Y) (evaluation (polynomial.obj Y)) (evaluation (polynomial.obj Y))
      (evaluationComparison (projection.app Y)) (evaluationComparison (projection.app Y))
      n s x)).trans (GlobalRawBass.inputComparisonHomotopy_cylinder g n r s _)

/-- The last original cylinder cell reverses only the inverse-chart evaluation height. -/
theorem native_upper (n : ℕ) (r s : unitInterval)
    (x : (prespectrum (globalModel.obj (op Y))).space n) :
    nativeFamily g n ((r, upper (upper s)), x) =
      (GlobalRawBass.minusSquareHomotopy g).level n
        (r, (evaluationComparison (projection.app Y)).level n (unitInterval.symm s, x)) :=
  (congrArg (fun y => (GlobalRawBass.inputComparisonHomotopy g).level n (r, y))
    (HomotopyPushout.mapOfHomotopies_upper_cell
      (sectionMap (projection.app Y)) (sectionMap (projection.app Y))
      (boundedFlatPerfectPrespectrumMap (projection.app Y))
      (boundedFlatPerfectPrespectrumMap (projection.app Y))
      (evaluation Y) (evaluation (polynomial.obj Y)) (evaluation (polynomial.obj Y))
      (evaluationComparison (projection.app Y)) (evaluationComparison (projection.app Y))
      n s x)).trans (GlobalRawBass.inputComparisonHomotopy_inr g n r _)

/-- The entire compact surface is exactly the original raw homotopy on span evaluation. -/
theorem whole_native (n : ℕ) :
    CommonReferenceNerve.compactPrespectrumFamily (InputMixedDesc.sourceMap g)
      (parameter g) n = nativeFamily g n := by
  apply ContinuousMap.ext
  rintro ⟨⟨r, s⟩, x⟩
  rcases three_cover s with ⟨t, rfl⟩ | ⟨t, rfl⟩ | ⟨t, rfl⟩
  · exact (CommonReferenceNerve.compactFamily_of_point_eq
      (InputMixedDesc.sourceMap g) (parameter g)
      (InputRawChartProductNodes.parameter g plus GlobalRawBass.plus_projection)
      (r, lower t) (t, r) (parameter_lower g r t) n x).trans
      ((DFunLike.congr_fun (InputRawChartProductNative.whole_native g plus
        GlobalRawBass.plus_projection n) ((t, r), x)).trans (native_lower g n r t x).symm)
  · exact (CommonReferenceNerve.compactFamily_of_point_eq
      (InputMixedDesc.sourceMap g) (parameter g) (InputRawDesc.parameter g)
      (r, upper (lower t)) (r, t) (parameter_middle g r t) n x).trans
      ((DFunLike.congr_fun (InputRawDesc.whole_native g n) ((r, t), x)).trans
        (native_middle g n r t x).symm)
  · exact (CommonReferenceNerve.compactFamily_of_point_eq
      (InputMixedDesc.sourceMap g) (parameter g)
      (InputRawChartProductNodes.parameter g minus GlobalRawBass.minus_projection)
      (r, upper (upper t)) (unitInterval.symm t, r) (parameter_upper g r t) n x).trans
      ((DFunLike.congr_fun (InputRawChartProductNative.whole_native g minus
        GlobalRawBass.minus_projection n) ((unitInterval.symm t, r), x)).trans
          (native_upper g n r t x).symm)

end Quillen.PerfectComplexes.GlobalBassEvaluation.InputRawPastedNative
