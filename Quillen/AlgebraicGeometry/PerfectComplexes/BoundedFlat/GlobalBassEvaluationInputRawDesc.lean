/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalRawBassInputDescNative
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalRawBassInputDescNodes
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveCompactPrecompAttachment
public import Quillen.Topology.Path.SimplexCollapsedEdges

/-!
# The complete original raw descent surface in the mixed evaluation reference

The entire original two-chart cancellation and quotient-collapse surface is attached through
the actual evaluation map. Whole continuous-map equalities retain its two times and native
input, without replacing it by a rectangle or a same-boundary filler.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.GlobalRawBass.InputDescSimplex
open GlobalSectionChangeIndex GlobalBassEvaluation
variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The actual evaluation embeds every complete geometric node in the mixed reference. -/
def mixedNodes (i : Fin 31) : InputChartReference.Node g :=
  InputDescNodes.evaluateNode g (nodes g i)

/-- Every original positive mixed node is retained by the complete diagram attachment. -/
theorem mixed_plus_nodes (i : Fin 18) :
    mixedNodes g (BassH0Diagram.plusFace.toOrderHom i) =
      InputChartReference.rawNode g plus plus_projection i :=
  (congrArg (InputDescNodes.evaluateNode g) (plus_nodes g i)).trans
    (InputDescNodes.raw_node_evaluate g plus plus_projection i).symm

/-- Every inverse mixed node is retained, including the actual shared evaluation anchors. -/
theorem mixed_minus_nodes (i : Fin 18) :
    mixedNodes g (BassH0Diagram.minusFace.toOrderHom i) =
      InputChartReference.rawNode g minus minus_projection i :=
  (congrArg (InputDescNodes.evaluateNode g) (minus_nodes g i)).trans
    (InputDescNodes.raw_node_evaluate g minus minus_projection i).symm


end Quillen.PerfectComplexes.GlobalRawBass.InputDescSimplex

namespace Quillen.PerfectComplexes.GlobalBassEvaluation.InputRawDesc
open GlobalSectionChangeIndex GlobalRawBass.InputDescSimplex
variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The unchanged raw descent parameter uses the complete original geometric node diagram. -/
def rawParameter :=
  (CommonReferenceNerve.parameter (reference g) (nodes g)).comp BassH0Diagram.parameter

/-- The raw native family uses the original ordering of both times and the prespectrum input. -/
def rawInputParameter (n : ℕ) :
    C((unitInterval × unitInterval) ×
      (originalPrespectrum (boundedFlatPerfectWaldhausen Y)).space n,
        unitInterval × (unitInterval ×
          (originalPrespectrum (boundedFlatPerfectWaldhausen Y)).space n)) :=
  ⟨fun z => (z.1.1, (z.1.2, z.2)), by fun_prop⟩

/-- Every point of the original raw quotient surface is retained as a whole continuous family. -/
theorem raw_whole_native (n : ℕ) :
    CommonReferenceNerve.compactPrespectrumFamily (reference g) (rawParameter g) n =
      ((GlobalRawBass.inputDescPasting g).toSquare.level n).comp
        (rawInputParameter (Y := Y) n) := by
  apply ContinuousMap.ext
  rintro ⟨⟨r, s⟩, x⟩
  exact (CommonReferenceNerve.compactPrespectrumFamily_eq_simplex
    (reference g) (rawParameter g) (nodes g) (r, s) (BassH0Diagram.parameter (r, s))
    rfl n x).trans
    ((congrArg (fun F => F (BassH0Diagram.parameter (r, s), x))
      (CommonReferenceNerve.prespectrumFamily_eq (reference g) (nodes g) n)).trans
      (square_native g n r s x))

/-- The full raw descent surface is attached by the original evaluation and its actual anchor. -/
def parameter :=
  (CommonReferenceNerve.mapParameter (GlobalRawBass.InputDescNodes.evaluateNode g)).comp
    (rawParameter g)

/-- Attachment is the entire characteristic surface of the already matched mixed nodes. -/
theorem parameter_eq : parameter g =
    (CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g) (mixedNodes g)).comp
      BassH0Diagram.parameter := by
  apply ContinuousMap.ext
  intro z
  exact CommonReferenceNerve.mapParameter_parameter
    (GlobalRawBass.InputDescNodes.evaluateNode g) (nodes g) (BassH0Diagram.parameter z)

/-- Evaluation changes only the original native input, leaving both surface times unchanged. -/
def evaluationInputParameter (n : ℕ) :
    C((unitInterval × unitInterval) × (prespectrum (globalModel.obj (op Y))).space n,
      (unitInterval × unitInterval) ×
        (originalPrespectrum (boundedFlatPerfectWaldhausen Y)).space n) :=
  ⟨fun z => (z.1, (prespectrumMap (evaluationModel (op Y))).map n z.2), by fun_prop⟩

/-- The entire original raw input descent square survives evaluation in the common mixed nerve. -/
theorem whole_native (n : ℕ) :
    CommonReferenceNerve.compactPrespectrumFamily (InputMixedDesc.sourceMap g) (parameter g) n =
      (((GlobalRawBass.inputDescPasting g).toSquare.level n).comp
        (rawInputParameter (Y := Y) n)).comp
        (evaluationInputParameter (Y := Y) n) :=
  (CommonReferenceNerve.compactPrespectrumFamily_attachPrecomp_map
    (reference g) (evaluationModel (op Y)) (InputMixedDesc.sourceMap g)
    (evaluationComparisonIso (laurent.map g ≫ GlobalRawBass.laurentProjection.app Y))
    (rawParameter g) n).trans
      (congrArg (fun F => F.comp (evaluationInputParameter (Y := Y) n)) (raw_whole_native g n))

/-- Every characteristic point of the positive rectangle keeps the complete mixed reference. -/
theorem plus_characteristic (z : StdSimplex ℝ (Fin 18)) :
    CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g) (mixedNodes g)
      (StdSimplex.map BassH0Diagram.plusFace.toOrderHom z) =
    CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g)
      (InputChartReference.rawNode g plus GlobalRawBass.plus_projection) z :=
  (CommonReferenceNerve.parameter_face (InputMixedDesc.sourceMap g) (mixedNodes g)
    BassH0Diagram.plusFace z).trans
    (congrArg (fun N => CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g) N z)
      (funext (mixed_plus_nodes g)))

/-- Every inverse characteristic point retains its separate chart and five actual shared nodes. -/
theorem minus_characteristic (z : StdSimplex ℝ (Fin 18)) :
    CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g) (mixedNodes g)
      (StdSimplex.map BassH0Diagram.minusFace.toOrderHom z) =
    CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g)
      (InputChartReference.rawNode g minus GlobalRawBass.minus_projection) z :=
  (CommonReferenceNerve.parameter_face (InputMixedDesc.sourceMap g) (mixedNodes g)
    BassH0Diagram.minusFace z).trans
    (congrArg (fun N => CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g) N z)
      (funext (mixed_minus_nodes g)))

open ProjectionRectangleParameters Quillen.SimplexParameters

/-- The complete positive raw-square edge retains its literal original scalar path. -/
theorem parameter_left (r : unitInterval) :
    parameter g (r, 0) =
      CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g) (mixedNodes g)
        (L BassH0Diagram.plusFace r) :=
  (DFunLike.congr_fun (parameter_eq g) (r, 0)).trans
    (congrArg (CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g) (mixedNodes g))
      (collapsed_left_path BassH0Diagram.boundaryParameter r))

/-- The inverse raw-square edge keeps its separate original scalar path. -/
theorem parameter_right (r : unitInterval) :
    parameter g (r, 1) =
      CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g) (mixedNodes g)
        (L BassH0Diagram.minusFace r) :=
  (DFunLike.congr_fun (parameter_eq g) (r, 1)).trans
    (congrArg (CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g) (mixedNodes g))
      (collapsed_right_path BassH0Diagram.boundaryParameter r))

/-- The source edge is the actual two-chart Bass path with its original half clock. -/
theorem parameter_zero (s : unitInterval) :
    parameter g (0, s) =
      CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g) (mixedNodes g)
        (((D BassH0Diagram.plusFace).symm.trans (D BassH0Diagram.minusFace)) s) :=
  (DFunLike.congr_fun (parameter_eq g) (0, s)).trans
    (congrArg (CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g) (mixedNodes g))
      (collapsed_zero_path BassH0Diagram.boundaryParameter s))

/-- The complete target edge retains both polynomial-square tracks and every nested half clock. -/
theorem parameter_one (s : unitInterval) :
    parameter g (1, s) =
      CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g) (mixedNodes g)
        (((Ppath BassH0Diagram.plusFace).trans
          (((K BassH0Diagram.plusFace).symm.trans (K BassH0Diagram.minusFace)).trans
            (Ppath BassH0Diagram.minusFace).symm)) s) :=
  (DFunLike.congr_fun (parameter_eq g) (1, s)).trans
    (congrArg (CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g) (mixedNodes g))
      (collapsed_top_path BassH0Diagram.boundaryParameter s))

end Quillen.PerfectComplexes.GlobalBassEvaluation.InputRawDesc
